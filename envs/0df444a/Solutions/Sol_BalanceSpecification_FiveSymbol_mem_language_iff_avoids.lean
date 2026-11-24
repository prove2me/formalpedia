-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.mem_language_iff_avoids
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:28.635946+00:00
-- url     : https://prove2.me/submissions/3154e825-0cdc-43d8-a28c-6750f913580e

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_block_padded_zero
public import Theorems.Thm_BalanceSpecification_FiveSymbol_padded_mem_shift
public import Theorems.Thm_BalanceSpecification_language_avoids_forbidden


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (w : Word Alphabet) :
    w ∈ language shift ↔ ∀ j : ℕ, 1 ≤ j → ¬ forbiddenWord j <:+: w := by
  constructor
  · intro hw j hj
    exact language_avoids_forbidden hw (forbiddenWord j) ⟨j, hj, rfl⟩
  · intro hw
    exact ⟨padded w, padded_mem_shift hw, 0, block_padded_zero w⟩
end BalanceSpecification.FiveSymbol
