-- Prove2me | solution 1 for CircuitComplexity.existQuantify_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:02.840086+00:00
-- url     : https://prove2.me/submissions/3579bc83-9f0f-4d06-8400-ba709e7efa9b

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
theorem _root_.solution {f g : BitString (k + m) → Bool}
    (h : ∀ z, f z = true → g z = true) {y : BitString m} :
    existQuantify f y = true → existQuantify g y = true := by
  simp only [existQuantify_eq_true]
  rintro ⟨x, hx⟩
  exact ⟨x, h _ hx⟩
end CircuitComplexity
