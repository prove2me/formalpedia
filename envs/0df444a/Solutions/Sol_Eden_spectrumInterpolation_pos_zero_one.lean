-- Prove2me | solution 1 for Eden.spectrumInterpolation_pos_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:49.562812+00:00
-- url     : https://prove2.me/submissions/a4e26f48-c9ca-4f96-b868-19e77d9373fc

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_LimitingInterpolation
import Theorems.Thm_Eden_exists_dimension_segment
import Theorems.Thm_Eden_spectrumInterpolation_interpolate


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c d : ℝ}
    (hd : d ∈ Ioo 0 3) : 0 < spectrumInterpolation ![2, 0, -2, -2, -c] d := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment
    (show d ∈ Icc 0 5 from ⟨hd.1.le, by linarith [hd.2]⟩)
  rw [spectrumInterpolation_interpolate _ hk hα.1 hα.2]
  interval_cases k <;>
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
  all_goals linarith [hα.1, hα.2, hd.1, hd.2]
end Eden
