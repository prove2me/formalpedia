-- Prove2me | solution 1 for BalanceSpecification.irreducible_of_hasVariableSpecification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:12.688726+00:00
-- url     : https://prove2.me/submissions/74187aef-bccc-468e-9386-ea0d92f08b96

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
    {X : ShiftSpace A} (h : HasVariableSpecification X) : Irreducible X := by
  obtain ⟨N, hN⟩ := h
  intro u hu v hv
  obtain ⟨w, hw, _, huv⟩ := hN u hu v hv
  exact ⟨w, hw, huv⟩
end BalanceSpecification
