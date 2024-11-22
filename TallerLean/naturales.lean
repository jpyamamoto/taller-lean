
inductive Natural where
  | zero : Natural
  | succ : Natural → Natural
  deriving Repr

#check Natural

def add (m : Natural) (n : Natural) : Natural :=
  match n with
  | Natural.zero   => m
  | Natural.succ n => Natural.succ (add m n)

#check add

def mul (m n : Natural) : Natural :=
  match n with
  | Natural.zero  => Natural.zero
  | Natural.succ n => add m (mul m n)

#check mul

open Natural

#eval add (succ (succ zero)) (succ zero)
#eval mul (succ (succ zero)) (succ zero)

#check Natural.recOn

theorem zero_add' (n : Natural) : (add zero n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    simp [add]
    assumption

#print zero_add'

def ejemplo (n : Natural) := Natural.recOn (motive := fun x => (add zero x) = x) n

#check ejemplo

theorem zero_add (n : Natural) : (add zero n) = n := 
  Natural.recOn (motive := fun x => (add zero x) = x) n
    rfl
    (fun n ih => by simp [add]; assumption)

#print zero_add
#check succ.injEq

theorem succ_add (m n : Natural) : (add m.succ n) = (add m n).succ := by
  induction n with
  | zero => simp [add]
  | succ n' ih => simp [add]; apply ih

theorem add_comm (m n : Natural) : (add m n) = (add n m) :=
  Natural.recOn m
    (by simp [add, zero_add])
    (fun m' ih => by 
      simp [add]
      rw [succ_add, ih]
      )

theorem one_mul' (n : Natural) : (mul n (succ zero)) = n := by
  simp [mul, add]

theorem one_mul (n : Natural) : (mul n (succ zero)) = n := by
  induction n with
  | zero => simp [mul, add]
  | succ n' _ => simp [mul, add]

theorem mul_one (n : Natural) : (mul (succ zero) n) = n := by
  induction n with
  | zero => simp [mul, add]
  | succ n' ih => simp [mul]; rw [succ_add, ih, zero_add] 

inductive BinaryTree where
  | leaf : BinaryTree
  | node : Natural -> BinaryTree → BinaryTree → BinaryTree

open BinaryTree

def size (b : BinaryTree) : Natural :=
  match b with
  | leaf => zero
  | node _ l r => succ (add (size l) (size r))

theorem empty_binary_tree (b : BinaryTree) : b = leaf ↔ size b = zero := by
  constructor
  . intro h
    rw [h]
    rfl
  . intro h
    cases b
    . rfl
    . simp [size] at h

#check Repr

