-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:32:03.160013+00:00
-- url     : https://prove2.me/submissions/488ab9e0-60fb-4c0d-a959-fe18094df853

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_primitive_deriv_positive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- The source scale primitive has one more positive-axis derivative than W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 2
      (fun x : ℝ => ∫ t in (0 : ℝ)..x, W t) (Ioi (0 : ℝ)) := by
  let U : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, W t
  have hdiff : DifferentiableOn ℝ U (Ioi (0 : ℝ)) := by
    intro x hx
    have hint : IntervalIntegrable W volume (0 : ℝ) x :=
      scaleFunction_intervalIntegrable_nonnegative X q W hW 0 x
        (le_refl 0) (le_of_lt hx)
    have hcont : ContinuousAt W x :=
      scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)
    have hmeas : StronglyMeasurableAtFilter W (nhds x) volume :=
      (chat04_scaleFunction_measurable_of_punctured_continuity
        X q W hW).aestronglyMeasurable.stronglyMeasurableAtFilter
    exact (integral_hasDerivAt_right hint hmeas hcont).differentiableAt.differentiableWithinAt
  have hWcd : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hD : ContDiffOn ℝ 1 (deriv U) (Ioi (0 : ℝ)) := by
    apply hWcd.congr
    intro x hx
    exact scaleFunction_primitive_deriv_positive X q W hW x hx
  have hC2 : ContDiffOn ℝ (1 + 1) U (Ioi (0 : ℝ)) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hdiff, ?_, hD⟩
    intro heq
    norm_num at heq
  simpa only [U, one_add_one_eq_two] using hC2
