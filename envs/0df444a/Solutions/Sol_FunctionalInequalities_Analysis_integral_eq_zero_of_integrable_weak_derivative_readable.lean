-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:21.133632+00:00
-- url     : https://prove2.me/submissions/9277929d-f78b-45bc-98fb-fd6e0b0eb336

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaled (E := E) R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    scaled_eq_zero hR (by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact le_of_lt (not_le.mp hx))
end FiniteDimensional
end
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section IntegrableWeakDivergence
open MeasureTheory Filter
open scoped ContDiff Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
set_option maxHeartbeats 800000 in
/-- The integral of a globally integrable weak directional derivative is zero.
This is the cutoff lemma used for Letwin arXiv:2607.24164v1 (2.1)/Lemma2.7. -/
theorem solution {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hweak : FunctionalInequalities.Analysis.HasWeakDerivAlong f g v)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, g x ∂volume) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  have hscaledNorm (R : ℝ) (x : E) : ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled R x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg R x)]
    exact FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one R x
  have hevent (x : E) : ∀ᶠ k : ℕ in atTop, ‖x‖ < (k : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun k hk => ?_⟩
    exact lt_of_le_of_lt (hN.trans (Nat.cast_le.mpr hk)) (lt_add_one _)
  have hcutLim :
      Tendsto
        (fun k : ℕ => ∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1) x * g x ∂volume)
        atTop (𝓝 (∫ x, g x ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun k =>
        ((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.continuous_scaled ((k : ℝ) + 1)).aestronglyMeasurable.mul
          hg.aestronglyMeasurable))
      hg.norm
    · intro k
      filter_upwards [] with x
      change ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1) x * g x‖ ≤ ‖g x‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm _ x)
    · filter_upwards [] with x
      have heq :
          (fun k : ℕ => FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1) x * g x) =ᶠ[atTop] fun _ => g x := by
        filter_upwards [hevent x] with k hk
        rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_eq_one (by positivity) hk.le, one_mul]
      exact tendsto_const_nhds.congr' heq.symm
  obtain ⟨M, hM0, hM⟩ := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_bound_fderiv_bump (E := E)
  have hcof (k : ℕ) (x : E) :
      ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v‖ ≤ M * ‖v‖ := by
    have hR : 0 < (k : ℝ) + 1 := by positivity
    have hi : ((k : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
    have hd : ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x‖ ≤ M :=
      (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_fderiv_scaled_le hR hM x).trans
        (mul_le_of_le_one_left hM0 hi)
    exact ((fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg v))
  have hderivLim :
      Tendsto
        (fun k : ℕ =>
          ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v * f x ∂volume)
        atTop (𝓝 0) := by
    have ht :
        Tendsto
          (fun k : ℕ =>
            ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v * f x ∂volume)
          atTop
          (𝓝 (∫ _x : E, (0 : ℝ) ∂volume)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => (M * ‖v‖) * ‖f x‖)
        (fun k =>
          (((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled ((k : ℝ) + 1)).continuous_fderiv (by simp)).clm_apply
            continuous_const).aestronglyMeasurable.mul hf.aestronglyMeasurable)
        (hf.norm.const_mul (M * ‖v‖))
      · intro k
        filter_upwards [] with x
        change ‖fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v * f x‖ ≤
          M * ‖v‖ * ‖f x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hcof k x) (norm_nonneg _)
      · filter_upwards [] with x
        have heq :
            (fun k : ℕ =>
              fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v * f x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
          filter_upwards [hevent x] with k hk
          rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.fderiv_scaled_eq_zero (by positivity) hk]
          simp only [zero_apply, zero_mul]
        exact tendsto_const_nhds.congr' heq.symm
    simpa only [integral_zero] using ht
  have hidentity (k : ℕ) :
      (∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1) x * g x ∂volume) =
        -(∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v * f x ∂volume) := by
    let R : ℝ := (k : ℝ) + 1
    have hR : 0 < R := by
      dsimp only [R]
      positivity
    have hχ : ContDiff ℝ 1 (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R) :=
      (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled R).of_le (by simp)
    have hw := hweak.2.2 (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R) hχ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled hR)
    have hfd :
        (∫ x, f x * fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R) x v ∂volume) =
          ∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R) x v * f x ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    have hgc :
        (∫ x, g x * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R x ∂volume) =
          ∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled (E := E) R x * g x ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    dsimp only [R] at hfd hgc hw ⊢
    linarith
  have hzero :
      Tendsto
        (fun k : ℕ => ∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1) x * g x ∂volume)
        atTop (𝓝 0) := by
    have hneg :
        Tendsto
          (fun k : ℕ =>
            -(∫ x, fderiv ℝ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((k : ℝ) + 1)) x v * f x ∂volume))
          atTop (𝓝 (-0)) :=
      hderivLim.neg
    simpa only [neg_zero] using
      hneg.congr' (Filter.Eventually.of_forall fun k => (hidentity k).symm)
  exact tendsto_nhds_unique hcutLim hzero
