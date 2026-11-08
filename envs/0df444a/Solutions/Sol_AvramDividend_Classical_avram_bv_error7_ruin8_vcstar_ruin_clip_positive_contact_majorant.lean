-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_ruin_clip_positive_contact_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:21:00.229619+00:00
-- url     : https://prove2.me/submissions/7bb5c741-6f2a-493a-a078-5998737aac75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Clipping the post-contact reserve at zero majorises the positive part of
the actual barrier-value change, including authentic ruin-crossing cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (z c : ℝ) (hz : 0 ≤ z) :
    max (vcstar W (z + c) - vcstar W z) 0 ≤
      max (vcstar W (max (z + c) 0) - vcstar W z) 0 := by
  rcases lt_or_ge (z + c) 0 with hcross | hstay
  · have hnegative : vcstar W (z + c) = 0 :=
      vcstar_eq_zero_of_neg W _ hcross
    have hnonneg : 0 ≤ vcstar W z :=
      avram_sweep17_vcstar_nonnegative_without_smoothness
        X hX q hq W hW hc z hz
    have hpart : max (vcstar W (z + c) - vcstar W z) 0 = 0 := by
      apply max_eq_right
      rw [hnegative]
      linarith
    rw [hpart]
    exact le_max_right _ _
  · rw [max_eq_left hstay]
