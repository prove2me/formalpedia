-- Prove2me | solution 1 for FunctionalInequalities.KLS.RegularPotential.integrable_exp_mul_norm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:06.761784+00:00
-- url     : https://prove2.me/submissions/9f95450f-c501-48e3-a762-b81e1dacbeaf

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : E → ℝ} {a b : ℝ}
omit [CompleteSpace E] in
private theorem FunctionalInequalities.KLS.RegularPotential.regularMoment_gaussian_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c * ‖x‖ ^ 2)) (volume : Measure E) := by
  have hb : 0 < (c : ℂ).re := by simpa using hc
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]
/-- The regular law has all exponential moments. -/
theorem solution (hV : FunctionalInequalities.KLS.RegularPotential V a b) (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) ((volume : Measure E).tilted (-V)) := by
  obtain ⟨C, hC, hdom⟩ := hV.exp_neg_le_gaussian
  let K : ℝ := 2 * r ^ 2 / a
  have hlin (x : E) : r * ‖x‖ ≤ a / 8 * ‖x‖ ^ 2 + K := by
    have hp := sq_nonneg (a * ‖x‖ - 4 * r)
    have he : K * a = 2 * r ^ 2 := div_mul_cancel₀ _ hV.pos.ne'
    apply (mul_le_mul_iff_right₀ hV.pos).mp
    nlinarith
  apply (integrable_tilted_iff hV.integrable_exp_neg _).2
  change Integrable (fun x => Real.exp ((-V) x) * Real.exp (r * ‖x‖))
    (volume : Measure E)
  refine ((FunctionalInequalities.KLS.RegularPotential.regularMoment_gaussian_integrable (E := E) (c := a / 8)
    (div_pos hV.pos (by norm_num))).const_mul (C * Real.exp K)).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp hV.temperate.1.continuous.neg).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_norm))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    calc
      Real.exp ((-V) x) * Real.exp (r * ‖x‖) ≤
          (C * Real.exp (-(a / 4) * ‖x‖ ^ 2)) * Real.exp (r * ‖x‖) :=
        mul_le_mul_of_nonneg_right (hdom x) (Real.exp_pos _).le
      _ = C * Real.exp (r * ‖x‖ - a / 4 * ‖x‖ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ C * Real.exp (K + (-(a / 8) * ‖x‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        linarith [hlin x]
      _ = (C * Real.exp K) * Real.exp (-(a / 8) * ‖x‖ ^ 2) := by
        rw [Real.exp_add]
        ring
