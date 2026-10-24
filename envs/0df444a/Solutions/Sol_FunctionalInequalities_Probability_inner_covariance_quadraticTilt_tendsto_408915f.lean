-- Prove2me | solution 1 for FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:22:58.072838+00:00
-- url     : https://prove2.me/submissions/eb4dcd37-0c63-441b-9b5b-b8f829dc5a19

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_FunctionalInequalities_Probability_integral_quadraticTilt_tendsto_408915f

noncomputable section
open MeasureTheory Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section Covariance
open ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Probability.weight_le_one {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    Real.exp (-(δ / 2) * ‖x‖ ^ 2) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (div_nonneg hδ (by norm_num))) (sq_nonneg _)
omit [CompleteSpace E] in
private theorem FunctionalInequalities.Probability.weight_integrable (μ : ProbabilityMeasure E) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun x : E => Real.exp (-(δ / 2) * ‖x‖ ^ 2)) (μ : Measure E) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact weight_le_one hδ x
omit [CompleteSpace E] in
/-- The quadratic tilt of a law with finite second moment has finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_quadraticTilt (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) {δ : ℝ} (hδ : 0 ≤ δ) :
    MemLp (id : E → E) 2 ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
  have hi : Integrable (fun x : E => ‖x‖ ^ 2) (μ : Measure E) := by
    simpa only [id_eq] using (memLp_two_iff_integrable_sq_norm hμ2.aestronglyMeasurable).mp hμ2
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (weight_integrable μ hδ) (fun x : E => ‖x‖ ^ 2)).mpr
  refine hi.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous (fun x : E => Real.exp (-(δ / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2)).aestronglyMeasurable
  · change ‖Real.exp (-(δ / 2) * ‖x‖ ^ 2) * ‖x‖ ^ 2‖ ≤ ‖x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (weight_le_one hδ x) (sq_nonneg _)).trans_eq (one_mul _)
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- `⟪Cov(μ_δ) u, v⟫ → ⟪Cov(μ) u, v⟫` as `δ → 0⁺` for the quadratic tilts `μ_δ = μ.tilted (−δ‖·‖²/2)`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) (u v : E) :
    Tendsto (fun δ : ℝ => ⟪FunctionalInequalities.Covariance.operator
      ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) u, v⟫)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪FunctionalInequalities.Covariance.operator (μ : Measure E) u, v⟫) := by
  let X : E → ℝ := fun x => ⟪u, x⟫
  let Y : E → ℝ := fun x => ⟪v, x⟫
  have hX : MemLp X 2 (μ : Measure E) := by simpa only [X, id_eq] using hμ2.const_inner (𝕜 := ℝ) u
  have hY : MemLp Y 2 (μ : Measure E) := by simpa only [Y, id_eq] using hμ2.const_inner (𝕜 := ℝ) v
  have hp := FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_408915f (μ : Measure E) (X * Y) (hX.integrable_mul hY)
  have hx := FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_408915f (μ : Measure E) X (hX.integrable one_le_two)
  have hy := FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_408915f (μ : Measure E) Y (hY.integrable one_le_two)
  have hlim := hp.sub (hx.mul hy)
  have hmean : ⟪FunctionalInequalities.Covariance.operator (μ : Measure E) u, v⟫ =
      (∫ x, (X * Y) x ∂(μ : Measure E)) - (∫ x, X x ∂(μ : Measure E)) * ∫ x, Y x ∂(μ : Measure E) := by
    rw [FunctionalInequalities.Covariance.operator_inner, covarianceBilin_apply_eq_cov hμ2, covariance_eq_sub hX hY]
  rw [hmean]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hd : 0 ≤ δ := (show 0 < δ from hδ).le
  let _ := FunctionalInequalities.Probability.isProbabilityMeasure_quadraticTilt (μ : Measure E) δ hd
  have hδ2 := FunctionalInequalities.Probability.memLp_id_two_quadraticTilt μ hμ2 hd
  have hδX : MemLp X 2 ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
    simpa only [X, id_eq] using hδ2.const_inner (𝕜 := ℝ) u
  have hδY : MemLp Y 2 ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
    simpa only [Y, id_eq] using hδ2.const_inner (𝕜 := ℝ) v
  rw [FunctionalInequalities.Covariance.operator_inner, covarianceBilin_apply_eq_cov hδ2, covariance_eq_sub hδX hδY]
