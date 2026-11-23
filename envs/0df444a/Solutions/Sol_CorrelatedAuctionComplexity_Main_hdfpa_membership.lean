-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.hdfpa_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:30:52.055797+00:00
-- url     : https://prove2.me/submissions/20ff2999-74ef-47a4-a31d-92ec300d26a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CorrelatedAuctionComplexity_Main_NashFixedSearch
import Theorems.Thm_CorrelatedAuctionComplexity_Main_expected_utility_polytime
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_weak_fixed_point_reduction
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_nash_map_endofline
import Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_membership_tfnp
import Theorems.Thm_ConstrSOSP_searchReduces_trans

set_option autoImplicit false

open CorrelatedAuctionComplexity.Main

theorem solution : InPPAD hVariableAccuracy := by
  refine ⟨hdfpa_membership_tfnp expected_utility_polytime, ?_⟩
  exact ConstrSOSP.searchReduces_trans hVariableAccuracy hNashFixedSearch EndOfLine
    hdfpa_weak_fixed_point_reduction
    (hdfpa_nash_map_endofline expected_utility_polytime)
