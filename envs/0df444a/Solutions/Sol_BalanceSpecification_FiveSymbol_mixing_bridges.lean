-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.mixing_bridges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:17.532877+00:00
-- url     : https://prove2.me/submissions/a513a7ec-ded4-4b3a-93ce-c0bd551fdc96

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_concat_twos_mem_language
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution : ∀ u ∈ language shift, ∀ v ∈ language shift,
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ b ∈ language shift, b.length = n ∧ u ++ b ++ v ∈ language shift := by
  intro u hu v hv
  refine ⟨u.length + 1, ?_⟩
  intro n hn
  have hconcat := concat_twos_mem_language hu hv (by omega : u.length < n)
  refine ⟨List.replicate n 2, ?_, List.length_replicate .., hconcat⟩
  exact language_factorial shift ⟨u, v, rfl⟩ hconcat
end BalanceSpecification.FiveSymbol
