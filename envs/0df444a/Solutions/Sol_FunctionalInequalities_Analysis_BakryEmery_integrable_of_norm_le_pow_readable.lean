-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:28.067804+00:00
-- url     : https://prove2.me/submissions/3abc3bac-d66f-466c-bb56-9a5a5cd12d73

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Under all exponential moments, polynomially bounded measurable functions are integrable. -/
theorem solution {F : Type*} [NormedAddCommGroup F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable g μ := by
    have hpow : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
        (1 + t) ^ n ≤ Real.exp ((n : ℝ) * t) := by
      intro t ht n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            (1 + t) ^ n.succ = (1 + t) ^ n * (1 + t) := by
              rw [pow_succ]
            _ ≤ Real.exp ((n : ℝ) * t) * Real.exp t := by
              exact
                mul_le_mul ih (by simpa [add_comm] using Real.add_one_le_exp t)
                  (by linarith) (by positivity)
            _ = Real.exp ((n.succ : ℕ) * t) := by
              rw [← Real.exp_add]
              congr 1
              push_cast
              ring
    have hdom : ∀ x : E, ‖g x‖ ≤ max C 0 * Real.exp ((k : ℝ) * ‖x‖) := by
      intro x
      have hp : (1 + ‖x‖) ^ k ≤ Real.exp ((k : ℝ) * ‖x‖) :=
        hpow ‖x‖ (norm_nonneg x) k
      calc
        ‖g x‖ ≤ C * (1 + ‖x‖) ^ k := hgb x
        _ ≤ max C 0 * (1 + ‖x‖) ^ k := by
          exact
            mul_le_mul_of_nonneg_right (le_max_left C 0)
              (pow_nonneg (by positivity) k)
        _ ≤ max C 0 * Real.exp ((k : ℝ) * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left hp (le_max_right C 0)
    refine ((hexp (k : ℝ)).const_mul (max C 0)).mono' hg
      (ae_of_all _ (fun x => ?_))
    simpa [smul_eq_mul] using hdom x
