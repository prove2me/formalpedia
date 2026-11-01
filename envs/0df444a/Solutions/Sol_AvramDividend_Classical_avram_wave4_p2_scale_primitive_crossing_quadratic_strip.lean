-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_quadratic_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:21:43.712984+00:00
-- url     : https://prove2.me/submissions/fbefc902-373f-41a7-a938-ae69e94ee320

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_crossing_signed_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_origin_crossing_strip_norm_integral_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- Actual finite-strip quadratic small-jump bound for the scale primitive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IntegrableOn
      (fun x : ℝ => |r * W x - ∫ t in (0 : ℝ)..x, W t|)
      (Ioo (0 : ℝ) r) ∧
      (∫ x in Ioo (0 : ℝ) r,
        |r * W x - ∫ t in (0 : ℝ)..x, W t|) ≤ W 1 * r ^ 2 := by
  let U : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, W t
  let F : ℝ → ℝ := fun x => r * W x - U x
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) r, |F x| ≤ W 1 * r := by
    intro x hx
    obtain ⟨h0, h1⟩ :=
      avram_wave4_p2_scale_primitive_crossing_signed_bound
        X q W hW r x hr0 hr1 hx.1 hx.2
    change |r * W x - U x| ≤ W 1 * r
    rw [abs_of_nonneg h0]
    simpa [mul_comm] using h1
  have hcont : ContinuousOn F (Ioo (0 : ℝ) r) := by
    intro x hx
    have hWcont : ContinuousAt W x :=
      scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx.1)
    have hint : IntervalIntegrable W volume (0 : ℝ) x :=
      scaleFunction_intervalIntegrable_nonnegative X q W hW 0 x
        (le_refl 0) (le_of_lt hx.1)
    have hmeas : StronglyMeasurableAtFilter W (nhds x) volume :=
      (chat04_scaleFunction_measurable_of_punctured_continuity
        X q W hW).aestronglyMeasurable.stronglyMeasurableAtFilter
    have hUcont : ContinuousAt U x := by
      exact (integral_hasDerivAt_right hint hmeas hWcont).continuousAt
    exact ((continuousAt_const.mul hWcont).sub hUcont).continuousWithinAt
  have hfinite : (volume : Measure ℝ) (Ioo (0 : ℝ) r) < ⊤ := by
    simp
  have hmeasF : AEStronglyMeasurable (fun x : ℝ => |F x|)
      (volume.restrict (Ioo (0 : ℝ) r)) :=
    hcont.abs.aestronglyMeasurable measurableSet_Ioo
  have hnorm : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) r)),
      ‖|F x|‖ ≤ W 1 * r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using hpoint x hx
  have hint : IntegrableOn (fun x : ℝ => |F x|) (Ioo (0 : ℝ) r) :=
    IntegrableOn.of_bound hfinite hmeasF (W 1 * r) hnorm
  have hstrip :=
    origin_crossing_strip_norm_integral_bound F (-r) (W 1)
      (by linarith) (by simpa using hint)
      (by
        intro x hx
        have hx' : x ∈ Ioo (0 : ℝ) r := by simpa only [neg_neg] using hx
        simpa only [neg_neg] using hpoint x hx')
  constructor
  · simpa only [F, U] using hint
  · simpa only [F, U, neg_neg, neg_sq] using hstrip
