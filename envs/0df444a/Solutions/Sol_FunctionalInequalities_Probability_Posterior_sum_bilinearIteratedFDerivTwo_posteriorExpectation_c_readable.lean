-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:47.447499+00:00
-- url     : https://prove2.me/submissions/6b644870-3644-490f-9336-23e811131126

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb
end
end
end

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- `∫ ⟪h, x⟫ dμ_{c,Q} = ⟪h, a⟫` (finite second moment from compact support). -/
theorem FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) = ⟪h, posteriorMean μ c Q⟫ := by
  obtain ⟨R, _hR, hmom⟩ := exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable μ hc
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have h2 : MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr (hmom c Q 2).1
  have hi := h2.integrable one_le_two
  change (∫ x, (innerSL ℝ h) (id x) ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
    (innerSL ℝ h) (∫ x, id x ∂((μ : Measure E).tilted (quadraticExponent c Q)))
  exact (innerSL ℝ h).integral_comp_comm hi
/-- The `c`-Hessian written with the posterior mean. -/
theorem FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_mean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        ⟪h, posteriorMean μ c Q⟫ * covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) -
        ⟪k, posteriorMean μ c Q⟫ * covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  rw [bilinearIteratedFDerivTwo_posteriorExpectation_c_readable μ hc hf hC hfb, integral_inner_eq_inner_posteriorMean μ hc c Q h,
    integral_inner_eq_inner_posteriorMean μ hc c Q k]
variable {ι : Type*} [Fintype ι]
/-- **Trace of the `c`-Hessian against a symmetric `M`**: `Σ_i D²_c(f)[M e_i, e_i] = Cov(f, ⟪Mx,x⟫) − 2 Cov(f, ⟪M a, x⟫)`
in any orthonormal basis. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q M : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
    (∑ i, bilinearIteratedFDerivTwo ℝ (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) c (M (b i)) (b i)) =
      covariance f (fun x => ⟪M x, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) -
        2 * covariance f (fun x => ⟪M (FunctionalInequalities.Probability.Posterior.posteriorMean μ c Q), x⟫)
          ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) := by
  let ν : Measure E := (μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)
  let a : E := FunctionalInequalities.Probability.Posterior.posteriorMean μ c Q
  let : IsProbabilityMeasure ν := FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  have hF2 : MemLp f 2 ν := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ hf hfb
  have hL2 (g : E → ℝ) (hg : Continuous g) : MemLp g 2 ν :=
    FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact μ hc c Q hg
  have hs1 : (∑ i, covariance f (fun x : E => ⟪M (b i), x⟫ * ⟪b i, x⟫) ν) =
      covariance f (fun x => ⟪M x, x⟫) ν := by
    rw [← covariance_fun_sum_right (fun i => hL2 _ (by fun_prop)) hF2]
    congr 1
    funext x
    calc
      ∑ i, ⟪M (b i), x⟫ * ⟪b i, x⟫ =
          ∑ i, ⟪M (⟪b i, x⟫ • b i), x⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_smul, real_inner_smul_left]
        ring
      _ = ⟪M (∑ i, ⟪b i, x⟫ • b i), x⟫ := by rw [map_sum, sum_inner]
      _ = ⟪M x, x⟫ := by rw [b.sum_repr' x]
  have hs2 : (∑ i, ⟪M (b i), a⟫ * covariance f (fun x : E => ⟪b i, x⟫) ν) =
      covariance f (fun x => ⟪M a, x⟫) ν := by
    simp_rw [← covariance_const_mul_right]
    rw [← covariance_fun_sum_right (fun i => hL2 _ (by fun_prop)) hF2]
    congr 1
    funext x
    calc
      (∑ i, ⟪M (b i), a⟫ * ⟪b i, x⟫) =
          ∑ i, ⟪M a, b i⟫ * ⟪b i, x⟫ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hM (b i) a, real_inner_comm (b i) (M a)]
      _ = ⟪M a, x⟫ := b.sum_inner_mul_inner (M a) x
  have hs3 : (∑ i, ⟪b i, a⟫ * covariance f (fun x : E => ⟪M (b i), x⟫) ν) =
      covariance f (fun x => ⟪M a, x⟫) ν := by
    simp_rw [← covariance_const_mul_right]
    rw [← covariance_fun_sum_right (fun i => hL2 _ (by fun_prop)) hF2]
    congr 1
    funext x
    calc
      ∑ i, ⟪b i, a⟫ * ⟪M (b i), x⟫ = ∑ i, ⟪M (⟪b i, a⟫ • b i), x⟫ := by
        simp only [map_smul, real_inner_smul_left]
      _ = ⟪M (∑ i, ⟪b i, a⟫ • b i), x⟫ := by rw [map_sum, sum_inner]
      _ = ⟪M a, x⟫ := by rw [b.sum_repr' a]
  simp_rw [FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_mean μ hc hf hC hfb]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  change (∑ i, covariance f (fun x : E => ⟪M (b i), x⟫ * ⟪b i, x⟫) ν) -
      (∑ i, ⟪M (b i), a⟫ * covariance f (fun x : E => ⟪b i, x⟫) ν) -
      (∑ i, ⟪b i, a⟫ * covariance f (fun x : E => ⟪M (b i), x⟫) ν) = _
  rw [hs1, hs2, hs3]
  ring
