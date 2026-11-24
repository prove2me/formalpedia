-- Prove2me | solution 1 for BalanceSpecification.interiorLanguage_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:57.943703+00:00
-- url     : https://prove2.me/submissions/9bbd3e63-41f0-41b3-afe9-408eac0ae291

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} (hL : IsFactorial L) (M : ℕ) :
    interiorLanguage L M ⊆ L := by
  rintro w ⟨p, q, _, _, hw⟩
  exact hL ⟨p, q, rfl⟩ hw
end BalanceSpecification
