-- Prove2me | solution 1 for BalanceSpecification.hasVariableSpecification_of_hasSpecification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:12.178808+00:00
-- url     : https://prove2.me/submissions/74aa08f3-4f57-49ed-a619-fe8be6721256

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Language

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {A : Type*} [TopologicalSpace A]
    {X : ShiftSpace A} (h : HasSpecification X) : HasVariableSpecification X := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro u hu v hv
  obtain ⟨w, hw, hlen, huv⟩ := hN u hu v hv
  exact ⟨w, hw, hlen.le, huv⟩
end BalanceSpecification
