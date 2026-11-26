-- Prove2me | solution 1 for Eden.periodicGlobalGrowthRate_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:56.404807+00:00
-- url     : https://prove2.me/submissions/ad09f167-4ce1-4de3-885a-035e31278b23

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_periodicGlobalGrowthRate_eq

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    (fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c] := by
  funext k
  rw [periodicGlobalGrowthRate_eq hc (by omega)]
  fin_cases k <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
  all_goals ring
end Eden
