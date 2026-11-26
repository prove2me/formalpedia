-- Prove2me | solution 1 for Eden.kaplanYorkeDimension_one_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:22.009369+00:00
-- url     : https://prove2.me/submissions/50fe40ea-55d5-4fa4-abf3-918b92726c70

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_between
import Theorems.Thm_Eden_kaplanYorkeIndex_eq


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c := by
  have hi : kaplanYorkeIndex ![2, 2, 0, 0, -c] = 4 := by
    apply kaplanYorkeIndex_eq (by omega)
      (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
    intro k hk hk₅
    have : k = 5 := by omega
    subst k
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
    linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ,
    abs_of_neg (show -c < 0 by linarith), targetDimension]
end Eden
