-- Prove2me | solution 2 for CorrelatedAuctionComplexity.Main.ppad_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:23:24.333597+00:00
-- url     : https://prove2.me/submissions/c47fe8d1-2031-4984-bd9e-52cf85850754
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_ppad_complete
import Theorems.Thm_CorrelatedAuctionComplexity_Main_dfpa_membership
import Theorems.Thm_CorrelatedAuctionComplexity_Main_suppress_zero_bids
import Theorems.Thm_CorrelatedAuctionComplexity_Main_dfpa_fixed_accuracy_membership
import Theorems.Thm_CorrelatedAuctionComplexity_Main_dfpa_hardness_transfer
import Theorems.Thm_CorrelatedAuctionComplexity_Main_utilityQ_eq_tie_dp
import Theorems.Thm_CorrelatedAuctionComplexity_Main_tie_dp_polytime
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_weak_fixed_point_reduction
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_nash_map_endofline

set_option autoImplicit false

open CorrelatedAuctionComplexity.Main

theorem solution :
    ∃ ε : ℚ, 0 < ε ∧ PPADComplete (dAuctionSearch ε) ∧ PPADHard (dAuctionSearch ε true) := by
  obtain ⟨δ, hδ, _hcomplete, hhard⟩ := hdfpa_ppad_complete
  let η : ℚ := 4 * δ
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hnorm : normalizedHAccuracy η = δ := by
    simp only [normalizedHAccuracy, η]
    ring
  have hhardH : PPADHard (hAuctionSearch (normalizedHAccuracy η) true) := by
    rwa [hnorm]
  obtain ⟨hgeneral, hrestricted⟩ := dfpa_hardness_transfer η hη hhardH
  have hε : 0 < normalizedDAccuracy η := by
    unfold normalizedDAccuracy
    positivity
  exact ⟨normalizedDAccuracy η, hε,
    ⟨dfpa_fixed_accuracy_membership _ hε, hgeneral⟩, hrestricted⟩
