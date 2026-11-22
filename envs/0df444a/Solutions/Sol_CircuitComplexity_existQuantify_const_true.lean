-- Prove2me | solution 1 for CircuitComplexity.existQuantify_const_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:17.850653+00:00
-- url     : https://prove2.me/submissions/27e785cb-0d41-4077-b9a9-7a2414f354fd

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
theorem _root_.solution :
    existQuantify (k := k) (m := m) (fun _ => true) = fun _ => true := by
  funext y; simp [existQuantify]
end CircuitComplexity
