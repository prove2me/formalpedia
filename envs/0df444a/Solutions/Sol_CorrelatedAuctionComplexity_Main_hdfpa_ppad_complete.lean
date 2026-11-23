-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.hdfpa_ppad_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:44:13.955408+00:00
-- url     : https://prove2.me/submissions/0ad407bd-365c-4a64-b49a-36859aa7750c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_fixed_accuracy_membership
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_hardness

set_option autoImplicit false

open CorrelatedAuctionComplexity.Main

theorem solution :
    ∃ ε : ℚ, 0 < ε ∧ PPADComplete (hAuctionSearch ε) ∧ PPADHard (hAuctionSearch ε true) := by
  obtain ⟨ε, hε, hhard, hrestricted⟩ := hdfpa_hardness
  exact ⟨ε, hε, ⟨hdfpa_fixed_accuracy_membership ε hε, hhard⟩, hrestricted⟩
