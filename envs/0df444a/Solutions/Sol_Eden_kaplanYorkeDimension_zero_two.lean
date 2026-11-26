-- Prove2me | solution 1 for Eden.kaplanYorkeDimension_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:20.871611+00:00
-- url     : https://prove2.me/submissions/4145d477-2707-4f87-b55a-a37a135f64e1

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
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 := by
  have hi : kaplanYorkeIndex ![0, -2, -2, -4, -c] = 1 := by
    apply kaplanYorkeIndex_eq (by omega) (by norm_num [spectrumPartialSum, spectrumEntry])
    intro k hk hk₅
    interval_cases k <;>
      norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
    all_goals linarith
  rw [kaplanYorkeDimension_of_index_between hi (by omega) (by omega)]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
end Eden
