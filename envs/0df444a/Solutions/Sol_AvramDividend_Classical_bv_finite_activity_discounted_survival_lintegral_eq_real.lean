-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_discounted_survival_lintegral_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:42:32.454584+00:00
-- url     : https://prove2.me/submissions/0ab4da94-4a6c-4f31-a512-b9f32c1c4430

import Theorems.Thm_AvramDividend_Classical_bv_reflected_strict_survival_measure_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_first_jump_discount_survival_kernel_product
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The discounted strict-survival drift kernel is the ordinary real exponential
integral, after the exact first-jump law and nonnegative Tonelli conversion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    (∫⁻ t in Ioi (0 : ℝ),
      P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} *
        ENNReal.ofReal (X.drift * Real.exp (-(q * t))) ∂volume) =
    ENNReal.ofReal (∫ t : ℝ in Ioi (0 : ℝ),
      X.drift * Real.exp
        (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t) ∂volume) := by
  let rate : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  have hrate : 0 ≤ rate := ENNReal.toReal_nonneg
  have hd : 0 ≤ X.drift := le_of_lt (bv_standing_drift_pos X hStanding hBV).1
  have hqr : 0 < q + rate := add_pos_of_pos_of_nonneg hq hrate
  have hInt :
      IntegrableOn (fun t : ℝ => X.drift * Real.exp (-(q + rate) * t))
        (Ioi (0 : ℝ)) volume := by
    have h := integrableOn_exp_mul_Ioi
      (show -(q + rate) < 0 by linarith) (0 : ℝ)
    change Integrable
      (fun t : ℝ => X.drift * Real.exp (-(q + rate) * t))
      (volume.restrict (Ioi (0 : ℝ)))
    exact h.const_mul X.drift
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => X.drift * Real.exp (-(q + rate) * t)) :=
    Filter.Eventually.of_forall (fun t => mul_nonneg hd (le_of_lt (Real.exp_pos _)))
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} *
        ENNReal.ofReal (X.drift * Real.exp (-(q * t))) ∂volume) =
      (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (X.drift * Real.exp (-(q + rate) * t))
          ∂volume) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [bv_reflected_strict_survival_measure_exp_first_jump
        X hStanding hBV hFinite t ht0]
      simpa only [rate, mul_comm t rate, neg_mul] using
        first_jump_discount_survival_kernel_product X.drift q rate t
    _ = ENNReal.ofReal
      (∫ t : ℝ in Ioi (0 : ℝ),
        X.drift * Real.exp (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t)
          ∂volume) := by
      simpa only [rate] using
        (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm
