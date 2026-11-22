-- Prove2me | solution 1 for CircuitComplexity.forallQuantify_eq_not_existQuantify_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:56.648146+00:00
-- url     : https://prove2.me/submissions/2afacd56-9c8f-407d-84eb-46ce7b78b9e3

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
    forallQuantify f y = !(existQuantify (fun z => !(f z)) y) := by
  unfold forallQuantify existQuantify
  cases h : decide (∀ x : BitString k, f (Fin.append x y) = true) <;>
    simp_all [decide_eq_false_iff_not, not_forall]
end CircuitComplexity
