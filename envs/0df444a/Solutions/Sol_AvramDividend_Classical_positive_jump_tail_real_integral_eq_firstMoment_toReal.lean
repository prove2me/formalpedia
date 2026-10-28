-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_real_integral_eq_firstMoment_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:03:13.74546+00:00
-- url     : https://prove2.me/submissions/0bce6d70-c0d5-4603-9e72-6e13c634509a

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The real integral of a finite-first-moment positive jump-tail density
is exactly the toReal of its ENNReal first moment (real layer cake). -/
theorem solution
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    (∫ t in Ioi (0 : ℝ),
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal ∂volume) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ).toReal := by
  let tail : ℝ → ℝ≥0∞ := fun t => μ {z : ℝ≥0 | t < (z : ℝ)}
  have hfinite : ∀ t : ℝ, 0 < t → tail t ≠ ⊤ := by
    intro t ht hinf
    have hbound :=
      positive_jump_tail_threshold_mass_le_first_moment μ t ht
    have ht0 : ENNReal.ofReal t ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr ht)
    change ENNReal.ofReal t * tail t ≤ _ at hbound
    rw [hinf, ENNReal.mul_top ht0] at hbound
    exact (not_lt_of_ge hbound) hfirst
  have htailInt : IntegrableOn (fun t : ℝ => (tail t).toReal)
      (Ioi (0 : ℝ)) volume := by
    simpa only [tail] using
      positive_jump_tail_real_integrable_of_finite_firstMoment μ hfirst
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => (tail t).toReal) :=
    Filter.Eventually.of_forall (fun t => ENNReal.toReal_nonneg)
  have hmass := positive_jump_tail_density_total_mass μ
  rw [withDensity_apply _ MeasurableSet.univ] at hmass
  have hlin :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((tail t).toReal)) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) := by
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), tail t := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact ENNReal.ofReal_toReal (hfinite t (mem_Ioi.mp ht))
      _ = _ := by simpa only [Measure.restrict_univ, tail] using hmass
  have hReal :
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), (tail t).toReal ∂volume) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) := by
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((tail t).toReal) :=
        ofReal_integral_eq_lintegral_ofReal htailInt hnonneg
      _ = _ := hlin
  have hintnonneg :
      0 ≤ ∫ t in Ioi (0 : ℝ), (tail t).toReal ∂volume :=
    integral_nonneg_of_ae hnonneg
  have h := congrArg ENNReal.toReal hReal
  simpa only [ENNReal.toReal_ofReal hintnonneg, tail] using h
