-- Prove2me | solution 2 for AvramDividend.Classical.positive_jump_tail_real_integral_eq_firstMoment_toReal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:03:24.595128+00:00
-- url     : https://prove2.me/submissions/c0d607a2-2ae0-4774-9e7a-76b72a4abdb1

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    (∫ t in Ioi (0 : ℝ),
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal ∂volume) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ).toReal := by
  have hanti : Antitone (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) := fun a b hab =>
    measure_mono fun z hz => lt_of_le_of_lt hab hz
  have hfin : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), μ {z : ℝ≥0 | t < (z : ℝ)} < ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [lt_top_iff_ne_top]
    intro htop
    have h := AvramDividend.Classical.positive_jump_tail_threshold_mass_le_first_moment μ a ha
    rw [htop, ENNReal.mul_top (by simpa using ha)] at h
    exact absurd (lt_of_le_of_lt h hfirst) (lt_irrefl _)
  rw [integral_toReal hanti.measurable.aemeasurable hfin,
    ← AvramDividend.Classical.positive_jump_tail_density_total_mass μ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
