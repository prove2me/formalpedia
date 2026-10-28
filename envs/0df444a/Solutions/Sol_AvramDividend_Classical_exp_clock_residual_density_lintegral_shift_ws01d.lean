-- Prove2me | solution 1 for AvramDividend.Classical.exp_clock_residual_density_lintegral_shift_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:05:30.3357+00:00
-- url     : https://prove2.me/submissions/24fcbc4b-22ce-4224-9510-da3c7b0ffdc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.LIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine real exponential density is memoryless under an arbitrary
nonnegative deterministic origin, for every measurable nonnegative reward.
The non-strict boundary is retained at the density level; it is atomless
for the genuine exponential observation measure. -/
theorem solution
    (p : ℝ) (hp : 0 < p) (a : ℝ≥0)
    (reward : ℝ → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ t : ℝ, if (a : ℝ) ≤ t then
       ProbabilityTheory.exponentialPDF p t * reward (t - (a : ℝ))
       else 0 ∂volume) =
    ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) *
      (∫⁻ u : ℝ, ProbabilityTheory.exponentialPDF p u *
        reward u ∂volume) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(p * (a : ℝ))))
  let g : ℝ → ℝ≥0∞ := fun u =>
    ProbabilityTheory.exponentialPDF p u * reward u
  have ha : (0 : ℝ) ≤ (a : ℝ) := a.property
  have hpdf : Measurable (ProbabilityTheory.exponentialPDF p) :=
    (ProbabilityTheory.measurable_exponentialPDFReal p).ennreal_ofReal
  have hg : Measurable g := hpdf.mul hr
  have hPDFshift (u : ℝ) (hu : 0 ≤ u) :
      ProbabilityTheory.exponentialPDF p (u + (a : ℝ)) =
        C * ProbabilityTheory.exponentialPDF p u := by
    rw [ProbabilityTheory.exponentialPDF_of_nonneg (add_nonneg hu ha),
      ProbabilityTheory.exponentialPDF_of_nonneg hu]
    change ENNReal.ofReal (p * Real.exp (-(p * (u + (a : ℝ))))) =
      ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) *
        ENNReal.ofReal (p * Real.exp (-(p * u)))
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    congr 1
    calc
      p * Real.exp (-(p * (u + (a : ℝ)))) =
          p * Real.exp (-(p * u) + -(p * (a : ℝ))) := by
            congr 1; ring
      _ = p * (Real.exp (-(p * u)) *
          Real.exp (-(p * (a : ℝ)))) := by rw [Real.exp_add]
      _ = Real.exp (-(p * (a : ℝ))) *
          (p * Real.exp (-(p * u))) := by ring
  have hPoint (t : ℝ) :
      (if (a : ℝ) ≤ t then
        ProbabilityTheory.exponentialPDF p t * reward (t - (a : ℝ))
       else 0) = C * g (t - (a : ℝ)) := by
    by_cases ht : (a : ℝ) ≤ t
    · rw [if_pos ht]
      have hu : 0 ≤ t - (a : ℝ) := sub_nonneg.mpr ht
      have hadd : (t - (a : ℝ)) + (a : ℝ) = t := by ring
      calc
        ProbabilityTheory.exponentialPDF p t *
          reward (t - (a : ℝ)) =
            ProbabilityTheory.exponentialPDF p
              ((t - (a : ℝ)) + (a : ℝ)) *
                reward (t - (a : ℝ)) := by rw [hadd]
        _ = (C * ProbabilityTheory.exponentialPDF p (t - (a : ℝ))) *
              reward (t - (a : ℝ)) := by
                rw [hPDFshift (t - (a : ℝ)) hu]
        _ = C * g (t - (a : ℝ)) := by
              dsimp [g]; ring
    · have hneg : t - (a : ℝ) < 0 := by linarith
      rw [if_neg ht]
      simp [g, ProbabilityTheory.exponentialPDF_of_neg hneg]
  have hshiftmeas : Measurable (fun t : ℝ => g (t - (a : ℝ))) :=
    hg.comp (measurable_id.sub measurable_const)
  calc
    _ = ∫⁻ t : ℝ, C * g (t - (a : ℝ)) ∂volume := by
      congr 1; funext t; exact hPoint t
    _ = C * (∫⁻ t : ℝ, g (t - (a : ℝ)) ∂volume) :=
      lintegral_const_mul C hshiftmeas
    _ = C * (∫⁻ u : ℝ, g u ∂volume) := by
      congr 1
      simpa only [sub_eq_add_neg] using
        (lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
          g (-(a : ℝ)))
    _ = _ := rfl
