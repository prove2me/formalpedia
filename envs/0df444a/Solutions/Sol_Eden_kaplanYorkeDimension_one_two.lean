-- Prove2me | solution 1 for Eden.kaplanYorkeDimension_one_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:22.870929+00:00
-- url     : https://prove2.me/submissions/1cc7000f-6137-40e8-a5f2-3ad6c347c9ce

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
    kaplanYorkeDimension ![2, 0, 0, -4, -c] = 7 / 2 := by
  have hi : kaplanYorkeIndex ![2, 0, 0, -4, -c] = 3 := by
    apply kaplanYorkeIndex_eq (by omega)
      (by norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ])
    intro k hk hk₅
    interval_cases k <;>
      norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
    all_goals linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
end Eden
