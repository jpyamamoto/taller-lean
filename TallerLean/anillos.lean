import Mathlib.RingTheory.Ideal.Basic

variable (R : Type*) [CommRing R]
variable (x y z : R)

example : x * 0 = 0 := by
  calc x * 0
    _ = x * 0 + 0 := by rw [add_zero]
    _ = x * 0 + (x * 0 + -(x * 0)) := by rw [add_neg_cancel]
    _ = (x * 0 + x * 0) + -(x * 0) := by rw [add_assoc]
    _ = x * (0 + 0) + -(x * 0)     := by rw [mul_add]
    _ = x * 0 + -(x * 0)           := by rw [add_zero]
    _ = 0                          := by rw [add_neg_cancel]

example : x * 0 = 0 := by
 rw [<-add_zero (x * 0)]
 nth_rw 2 [<-add_neg_cancel (x * 0)]
 rw [<-add_assoc, <-mul_add, add_zero, add_neg_cancel]


--Equivalencia de dominio entero
example (h : ∀ (c : R), c ≠ 0 → ∀ (a b : R), c * a = c * b → a = b) :
    ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b h'
  by_cases aiscero : a = 0
  · left; assumption
  · right
    apply h a
    · assumption
    · rw [mul_zero]; exact h'

example (h : ∀ (c : R), c ≠ 0 → ∀ (a b : R), c * a = c * b → a = b) :
    ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b h'
  by_cases biscero : b = 0
  · right; assumption
  · left
    apply h b
    · assumption
    · rw [mul_zero, mul_comm]; exact h'

#check congrArg
#check Eq.symm
#check mul_add
#check by_cases

example (h : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) :
    ∀ (c : R), c ≠ 0 → ∀ (a b : R), c * a = c * b → b = a := by
  intro c cnozero a b mulcleft
  have : (c * -a) + c * a = (c * -a) + c * b := by
    apply congrArg
    exact mulcleft
  simp only [<-mul_add] at this
  rw [neg_add_cancel, mul_zero] at this
  have : c * (-a + b) = 0 := by
    apply Eq.symm; assumption
  specialize h c (-a + b) this
  rcases h with ciszero | h'
  · contradiction
  · have : a + (-a + b) = a + 0 := by
      apply congrArg
      assumption
    simp at this
    assumption


class Grupo' (G : Type*) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x : G, mul one x = x
  inv_mul_cancel : ∀ x : G, mul (inv x) x = one

class Grupo (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ (x y z : G), x * y * z = x * (y * z)
  one_mul : ∀ x : G, 1 * x = x
  inv_mul_cancel : ∀ x : G, x⁻¹ * x = 1

variable (G : Type*) [Grupo G]
variable (x y z : G)

lemma foo1 (h : x * x = x) : x = 1 := by
  rw [<-Grupo.one_mul x, <-Grupo.inv_mul_cancel x]
  rw [Grupo.mul_assoc, h]

/-
Queremos demostrar x * x⁻¹ = 1
-/

lemma foo2 : (x * x⁻¹) * (x * x⁻¹) = x * x⁻¹ := by
  rw [Grupo.mul_assoc, <-Grupo.mul_assoc x⁻¹]
  rw [Grupo.inv_mul_cancel,Grupo.one_mul]

theorem Grupo.mul_inv_cancel : ∀ (x : G), x * x⁻¹ = 1 := by
  intro a
  apply foo1
  apply foo2

theorem Grupo.mul_one : ∀ (x : G), x * 1 = x := by
  intro a
  rw [<-Grupo.inv_mul_cancel a]
  rw [<-Grupo.mul_assoc]
  rw [Grupo.mul_inv_cancel _ a]
  rw [Grupo.one_mul]

#print Grupo.mul_one

theorem foo3 (h : x * y = x * z) : y = z := by
  rw [<-Grupo.one_mul y]
  rw [<-Grupo.inv_mul_cancel x]
  rw [Grupo.mul_assoc]
  rw [h]
  rw [<-Grupo.mul_assoc]
  rw [Grupo.inv_mul_cancel]
  rw [Grupo.one_mul]

example (h1 : x = z) (h2 : z = y) : x = y := by
  have : x = y := by
    rw [<-h1] at h2
    assumption
  --have : x = z := by sorry
  assumption

theorem foo4 : ∀ y : G, ∃ z : G, x * z = y := by
  intro a
  use x⁻¹ * a
  rw [<-Grupo.mul_assoc]
  rw [Grupo.mul_inv_cancel]
  rw [Grupo.one_mul]


inductive unitario where
  | unit

instance : Grupo (unitario) where
  mul _ _ := unitario.unit
  one := unitario.unit
  inv := λ _ ↦ unitario.unit
  mul_assoc := by simp
  one_mul := by simp
  inv_mul_cancel := by simp


def tres (x : G) := x * x * x

example : tres unitario unitario.unit = unitario.unit := by simp

#eval 1 + 1
#eval match unitario.unit * unitario.unit with | unitario.unit => 42
