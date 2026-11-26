-- Prove2me | solution 1 for Eden.globalGrowthIndex_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:26.624805+00:00
-- url     : https://prove2.me/submissions/7a040a13-0148-4c95-8ee9-cd57f84bbab5

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
import Theorems.Thm_Eden_spectrumPartialSum_globalGrowthIncrements
import Theorems.Thm_Eden_globalGrowthRate_five_neg
import Theorems.Thm_Eden_globalGrowthRate_four
import Theorems.Thm_Eden_kaplanYorkeIndex_eq


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 := by
  apply kaplanYorkeIndex_eq (by norm_num)
  · rw [spectrumPartialSum_globalGrowthIncrements hc.le (by norm_num), globalGrowthRate_four hc.le]
    norm_num
  · intro k hk hk₅
    have he : k = 5 := by omega
    subst k
    rw [spectrumPartialSum_globalGrowthIncrements hc.le le_rfl]
    exact globalGrowthRate_five_neg hc
end Eden
