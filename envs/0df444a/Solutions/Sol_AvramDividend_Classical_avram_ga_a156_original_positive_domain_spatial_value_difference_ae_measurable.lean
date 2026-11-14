-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a156_original_positive_domain_spatial_value_difference_ae_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:30:39.109784+00:00
-- url     : https://prove2.me/submissions/8d171dd7-be83-46fd-8205-912211f1ba90

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

/-- Actual Gaussian stopped positive-domain value differences remain a.e. measurable by continuous zero extension and cancellation of inactive outside-domain cells. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (Y Z E : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hE : Measurable E)
    (hAlt : ∀ᵐ ω ∂P, Y ω = Z ω ∨ (0 < Y ω ∧ 0 < Z ω)) :
    AEStronglyMeasurable
      (fun ω => E ω * (w (Z ω) - w (Y ω))) P := by
  classical
  let wPos : ℝ → ℝ := fun y => if 0 < y then w y else 0
  have hWPos : Measurable wPos := by
    change Measurable ((Ioi (0 : ℝ)).piecewise w (fun _ => 0))
    exact hw.measurable_piecewise continuous_const.continuousOn
      isOpen_Ioi.measurableSet
  have hMeasured : Measurable
      (fun ω => E ω * (wPos (Z ω) - wPos (Y ω))) :=
    hE.mul ((hWPos.comp hZ).sub (hWPos.comp hY))
  have hEq : (fun ω => E ω * (wPos (Z ω) - wPos (Y ω))) =ᵐ[P]
      (fun ω => E ω * (w (Z ω) - w (Y ω))) := by
    filter_upwards [hAlt] with ω hω
    rcases hω with hSame | ⟨hYpos,hZpos⟩
    · simp only [wPos, hSame, sub_self, mul_zero]
    · simp only [wPos, if_pos hYpos, if_pos hZpos]
  exact hMeasured.aestronglyMeasurable.congr hEq
