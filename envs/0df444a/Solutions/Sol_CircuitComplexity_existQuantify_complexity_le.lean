-- Prove2me | solution 1 for CircuitComplexity.existQuantify_complexity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:39.015404+00:00
-- url     : https://prove2.me/submissions/bdf5af51-5d02-48db-8380-7b6dba2857a9

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism
public import Theorems.Thm_CircuitComplexity_restrict_size_complexity_le
public import Theorems.Thm_CircuitComplexity_or_size_complexity_le
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_existQuantify_const_false
public import Theorems.Thm_CircuitComplexity_existQuantify_const_true
public import Theorems.Thm_CircuitComplexity_existQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_existQuantify_succ
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_false
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_eq_true
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth
attribute [local simp] CircuitComplexity.existQuantify_const_false
attribute [local simp] CircuitComplexity.existQuantify_const_true
attribute [local simp] CircuitComplexity.existQuantify_eq_true
attribute [local simp] CircuitComplexity.forallQuantify_const_false
attribute [local simp] CircuitComplexity.forallQuantify_const_true
attribute [local simp] CircuitComplexity.forallQuantify_eq_true


section
@[expose] public section
namespace CircuitComplexity
variable {k m : Nat}
private theorem size_complexity_cast {n n' : Nat} {B : Basis} [NeZero n] [NeZero n']
    (h : n = n') (f : BitString n → Bool) :
    Circuit.sizeComplexity B (h ▸ f : BitString n' → Bool) =
      Circuit.sizeComplexity B f := by
  subst h; rfl
private theorem cast_fun_apply {n n' : Nat}
    (h : n = n') (f : BitString n → Bool) (y : BitString n') :
    (h ▸ f) y = f (h.symm ▸ y) := by
  subst h; rfl
private theorem cast_fun_fin_apply {n n' : Nat}
    (h : n = n') (f : Fin n → Bool) (i : Fin n') :
    (h ▸ f) i = f (Fin.cast h.symm i) := by
  subst h; rfl
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤
      2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1) := by
  suffices h : Circuit.sizeComplexity Basis.andOr2 (existQuantify f) + 1 ≤
      2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1) by omega
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    suffices hle : Circuit.sizeComplexity Basis.andOr2 (existQuantify (k := 0) f) ≤
        Circuit.sizeComplexity Basis.andOr2 f by omega
    suffices heq : existQuantify (k := 0) f = (Nat.zero_add m) ▸ f by
      rw [heq, size_complexity_cast]
    funext y
    unfold existQuantify
    simp only [Unique.exists_iff, Bool.decide_eq_true]
    rw [cast_fun_apply]
    congr 1
    funext i
    simp only [Fin.append, Fin.addCases, not_lt_zero, ↓reduceDIte, Nat.add_zero, Fin.subNat_zero,
      eq_rec_constant]
    rw [cast_fun_fin_apply]
  | succ k ih =>
    have hfun : existQuantify (k := k + 1) f = fun y =>
        (existQuantify (k := k) (restrictFirst f false) y ||
         existQuantify (k := k) (restrictFirst f true) y) :=
      funext (existQuantify_succ f)
    rw [hfun]
    set g₁ := existQuantify (k := k) (restrictFirst f false)
    set g₂ := existQuantify (k := k) (restrictFirst f true)
    set s := Circuit.sizeComplexity Basis.andOr2 f
    have hor := or_size_complexity_le g₁ g₂
    have h₁ : Circuit.sizeComplexity Basis.andOr2 g₁ + 1 ≤ 2 ^ k * (s + 1) :=
      le_trans (ih (restrictFirst f false))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (restrict_size_complexity_le f false) 1))
    have h₂ : Circuit.sizeComplexity Basis.andOr2 g₂ + 1 ≤ 2 ^ k * (s + 1) :=
      le_trans (ih (restrictFirst f true))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (restrict_size_complexity_le f true) 1))
    calc Circuit.sizeComplexity Basis.andOr2 (fun y => g₁ y || g₂ y) + 1
        ≤ (Circuit.sizeComplexity Basis.andOr2 g₁ +
           Circuit.sizeComplexity Basis.andOr2 g₂ + 1) + 1 :=
          Nat.add_le_add_right hor 1
      _ = (Circuit.sizeComplexity Basis.andOr2 g₁ + 1) +
          (Circuit.sizeComplexity Basis.andOr2 g₂ + 1) := by omega
      _ ≤ 2 ^ k * (s + 1) + 2 ^ k * (s + 1) := Nat.add_le_add h₁ h₂
      _ = 2 ^ (k + 1) * (s + 1) := by ring
end CircuitComplexity
