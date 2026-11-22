-- Prove2me | solution 1 for CircuitComplexity.Schnorr.evalD_essential_means_referenced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:51.890808+00:00
-- url     : https://prove2.me/submissions/1b8a6077-c845-4236-b15d-78afd5e1f26d

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Theorems.Thm_CircuitComplexity_Schnorr_wireValD_eq_of_unreferenced
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution
    {N s : Nat} (d : CircDesc N s) (hs : 0 < s) (a : Fin N)
    (hdep : ∃ x : BitString N, evalD hs d x ≠ evalD hs d (Function.update x a (!x a))) :
    ∃ g : Fin s, (d g).2.1.1.val = a.val ∨ (d g).2.1.2.val = a.val := by
  by_contra hall; push Not at hall
  obtain ⟨x, hx⟩ := hdep; apply hx
  simp only [evalD]
  have hw : (⟨N + s - 1, by omega⟩ : Fin (N + s)).val ≠ a.val := by
    change N + s - 1 ≠ a.val; have := a.isLt; omega
  exact wireValD_eq_of_unreferenced d a (!x a)
    (fun g => ⟨(hall g).1, (hall g).2⟩) x ⟨N + s - 1, by omega⟩ hw
end CircuitComplexity.Schnorr
