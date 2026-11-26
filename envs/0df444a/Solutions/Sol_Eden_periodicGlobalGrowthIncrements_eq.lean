-- Prove2me | solution 1 for Eden.periodicGlobalGrowthIncrements_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:50.950199+00:00
-- url     : https://prove2.me/submissions/a403e31c-a96f-49d5-9fbe-ef2c04cb6e86

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthRate_eq


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    periodicGlobalGrowthIncrements c = ![2, 0, -2, -2, -c] := by
  funext i
  unfold periodicGlobalGrowthIncrements
  rw [periodicGlobalGrowthRate_eq hc (by omega), periodicGlobalGrowthRate_eq hc (by omega)]
  fin_cases i <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
end Eden
