-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_killed_scale_martingale_all_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:44:22.911535+00:00
-- url     : https://prove2.me/submissions/feab9363-9784-4b85-b053-924d770922a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_martingale
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_martingale_from_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by
  by_cases hBV : X.BoundedVariation
  · exact avram_ws01b_bv_killed_scale_martingale X hX q hq W hW hBV x
  · exact avram_root29_01_unbounded_killed_martingale_from_source X hBV q hq W hW x
