-- Prove2me | solution 1 for FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:22:10.507557+00:00
-- url     : https://prove2.me/submissions/68f35cf5-8c41-42d2-9c8e-dc23dd1c9837

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
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- **Normalized small quadratic tilts converge**: for a probability measure `μ` and an integrable
`f`, `∫ f d(μ tilted by e^{-δ‖x‖²/2}) → ∫ f dμ` as `δ → 0⁺`. -/
theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → F) (hf : Integrable f μ) :
    Tendsto
      (fun δ : ℝ => ∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
  let w : ℝ → E → ℝ := fun δ x => Real.exp (-(δ / 2) * ‖x‖ ^ 2)
  let Z : ℝ → ℝ := fun δ => ∫ x, w δ x ∂μ
  let I : ℝ → F := fun δ => ∫ x, w δ x • f x ∂μ
  have hw_cont (δ : ℝ) : Continuous (w δ) := by
    dsimp [w]
    fun_prop
  have hw_nonneg (δ : ℝ) (x : E) : 0 ≤ w δ x :=
    (Real.exp_pos _).le
  have hw_le (δ : ℝ) (hδ : 0 ≤ δ) (x : E) : w δ x ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg hδ (by norm_num))) (sq_nonneg _)
  have hw_lim (x : E) : Tendsto (fun δ : ℝ => w δ x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun δ : ℝ => w δ x) := by
      dsimp [w]
      fun_prop
    have ht : Tendsto (fun δ : ℝ => w δ x) (𝓝 (0 : ℝ)) (𝓝 (w 0 x)) :=
      hc.tendsto 0
    simpa [w] using ht.mono_left nhdsWithin_le_nhds
  have hZ : Tendsto Z (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := w) (f := fun _ : E => (1 : ℝ)) (fun _ : E => (1 : ℝ))
      (Filter.Eventually.of_forall fun δ => (hw_cont δ).aestronglyMeasurable) ?_
      (integrable_const 1) (Filter.Eventually.of_forall hw_lim)
    · simpa [Z] using h
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg δ x)]
        exact hw_le δ hδ.le x
  have hI : Tendsto I (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun δ x => w δ x • f x) (f := f) (fun x => ‖f x‖)
    · exact Filter.Eventually.of_forall fun δ =>
        (hw_cont δ).aestronglyMeasurable.smul hf.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ at hδ
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg δ x)]
        simpa using mul_le_mul_of_nonneg_right (hw_le δ hδ.le x) (norm_nonneg (f x))
    · exact hf.norm
    · exact Filter.Eventually.of_forall fun x => by
        simpa using (hw_lim x).smul (tendsto_const_nhds (x := f x))
  have hnormalized : Tendsto (fun δ => (Z δ)⁻¹ • I δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
    simpa using (hZ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).smul hI
  have heq (δ : ℝ) :
      (∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2))) =
        (Z δ)⁻¹ • I δ := by
    rw [MeasureTheory.integral_tilted]
    change (∫ x, (w δ x / Z δ) • f x ∂μ) = (Z δ)⁻¹ • I δ
    simp_rw [div_eq_mul_inv, mul_comm (w δ _) ((Z δ)⁻¹), mul_smul]
    exact integral_smul (Z δ)⁻¹ (fun x => w δ x • f x)
  simpa only [heq] using hnormalized
