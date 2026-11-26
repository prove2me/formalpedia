-- Prove2me | solution 1 for Eden.periodicGlobalGrowthRate_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:37.471445+00:00
-- url     : https://prove2.me/submissions/618ed1d3-86b7-49a5-98e4-b59065104110

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_tendsto_periodicGlobalLogGrowth_div

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalGrowthRate c k = spectrumPartialSum ![2, 0, -2, -2, -c] k :=
  (tendsto_periodicGlobalLogGrowth_div hc hk).limUnder_eq
end Eden
