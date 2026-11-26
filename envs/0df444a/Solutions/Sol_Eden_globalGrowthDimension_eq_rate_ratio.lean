-- Prove2me | solution 1 for Eden.globalGrowthDimension_eq_rate_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:17.402019+00:00
-- url     : https://prove2.me/submissions/d8b774af-3fcc-4038-9966-9a22154aaed9

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
import Theorems.Thm_Eden_globalGrowthDimension_eq_target
import Theorems.Thm_Eden_globalGrowthRate_five
import Theorems.Thm_Eden_globalGrowthRate_four


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    globalGrowthDimension c =
      4 + globalGrowthRate c 4 / (globalGrowthRate c 4 - globalGrowthRate c 5) := by
  rw [globalGrowthDimension_eq_target hc, globalGrowthRate_four hc.le, globalGrowthRate_five hc.le]
  congr 2
  ring
end Eden
