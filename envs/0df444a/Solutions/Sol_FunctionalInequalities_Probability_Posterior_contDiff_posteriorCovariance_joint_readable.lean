-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:11.148906+00:00
-- url     : https://prove2.me/submissions/bb6fef80-fbff-447e-9948-3eb161c2c49f

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_covariance_pair_joint_readable

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

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The posterior has finite second moment. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    MemLp id 2 (compactPosterior μ hc c Q : Measure E) := by
  change MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q))
  have hn : MemLp (fun x : E => ‖x‖) 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q continuous_norm
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
section Moments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An operator is the sum of its matrix entries times rank-one operators in a finite orthonormal
basis. -/
private theorem FunctionalInequalities.Probability.Posterior.operator_eq_sum_rankOne {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) :
    A = ∑ j, ∑ i, ⟪b i, A (b j)⟫ • InnerProductSpace.rankOne ℝ (b i) (b j) := by
  apply ContinuousLinearMap.ext
  intro x
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro j _hj
  conv_lhs => rw [← b.sum_repr' (A (b j)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul]
  congr 1
  ring
/-- **Joint smoothness of the posterior covariance** `A(c,Q) = Cov(μ_{c,Q})` on `E × (E →L[ℝ] E)`, in the
operator norm; no isotropy or symmetry of `Q` is needed. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E)) := by
  let b := stdOrthonormalBasis ℝ E
  have he (p : E × (E →L[ℝ] E)) (i j : Fin (Module.finrank ℝ E)) :
      ⟪b i, FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E) (b j)⟫ =
        covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
          ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) := by
    rw [real_inner_comm, FunctionalInequalities.Covariance.operator_inner,
      covarianceBilin_apply_eq_cov (FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two μ hc p.1 p.2)]
    rfl
  have hs : ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => ∑ j, ∑ i,
      covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) •
          InnerProductSpace.rankOne ℝ (b i) (b j)) :=
    ContDiff.sum (fun j _hj => ContDiff.sum (fun i _hi =>
      (FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_readable μ hc (b j) (b i)).smul contDiff_const))
  have hfun : (fun p : E × (E →L[ℝ] E) =>
      FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E)) =
      fun p => ∑ j, ∑ i, covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) •
          InnerProductSpace.rankOne ℝ (b i) (b j) := by
    funext p
    rw [FunctionalInequalities.Probability.Posterior.operator_eq_sum_rankOne b (FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure E))]
    simp only [he]
  rw [hfun]
  exact hs
