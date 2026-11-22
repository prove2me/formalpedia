-- Prove2me | solution 1 for CircuitComplexity.existQuantify_eq_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:06.287543+00:00
-- url     : https://prove2.me/submissions/ccee1c56-870f-4df9-a6ef-33e85773fa9a

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution {f : BitString (k + m) → Bool} {y : BitString m} :
    existQuantify f y = true ↔ ∃ x : BitString k, f (Fin.append x y) = true := by
  simp [existQuantify]
end CircuitComplexity
