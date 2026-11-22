-- Prove2me | solution 1 for CircuitComplexity.existQuantify_eq_not_forallQuantify_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:59.98954+00:00
-- url     : https://prove2.me/submissions/1bed7f4d-6e9c-4096-9a92-375909406a6b

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Theorems.Thm_CircuitComplexity_existQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


attribute [local simp] CircuitComplexity.existQuantify_eq_true
attribute [local simp] CircuitComplexity.forallQuantify_eq_true

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution
    (f : BitString (k + m) → Bool) (y : BitString m) :
    existQuantify f y = !(forallQuantify (fun z => !(f z)) y) := by
  unfold existQuantify forallQuantify
  cases h : decide (∃ x : BitString k, f (Fin.append x y) = true) <;>
    simp_all [decide_eq_false_iff_not, not_exists]
end CircuitComplexity
