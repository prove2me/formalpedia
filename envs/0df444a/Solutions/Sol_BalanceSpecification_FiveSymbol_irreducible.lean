-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:04.606871+00:00
-- url     : https://prove2.me/submissions/b00fcecb-3923-4ed5-9c91-4b376aa9ed9c

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mixing_bridges

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution : Irreducible shift := by
  intro u hu v hv
  obtain ⟨N, hN⟩ := mixing_bridges u hu v hv
  obtain ⟨b, hb, _, hconcat⟩ := hN N le_rfl
  exact ⟨b, hb, hconcat⟩
end BalanceSpecification.FiveSymbol
