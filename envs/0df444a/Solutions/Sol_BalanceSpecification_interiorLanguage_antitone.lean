-- Prove2me | solution 1 for BalanceSpecification.interiorLanguage_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:02.289221+00:00
-- url     : https://prove2.me/submissions/4accb8a1-123f-45ad-9c60-383b426db3e5

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
theorem _root_.solution {L : Set (Word A)} {M N : ℕ} (hMN : M ≤ N) :
    interiorLanguage L N ⊆ interiorLanguage L M := by
  rintro w ⟨p, q, hp, hq, hw⟩
  exact ⟨p, q, hMN.trans hp, hMN.trans hq, hw⟩
end BalanceSpecification
