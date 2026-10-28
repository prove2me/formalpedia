-- Prove2me | solution 1 for FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:34.761534+00:00
-- url     : https://prove2.me/submissions/dc6e5f9d-5abb-43c1-91b9-7b33107deccf

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Theorems.Thm_FunctionalInequalities_Probability_covariance_sq_le_variance_mul_variance_readable

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
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section TiltAbsoluteContinuity
variable {Ω : Type*} [MeasurableSpace Ω]
/-- A normalized tilt has the same topological support as the base law. -/
theorem FunctionalInequalities.Probability.support_tilted_eq [TopologicalSpace Ω] (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) : (μ.tilted φ).support = μ.support :=
  Set.Subset.antisymm (tilted_absolutelyContinuous μ φ).support_mono
    (absolutelyContinuous_tilted hi).support_mono
end TiltAbsoluteContinuity
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
/-- The posterior has the same support as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_support (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    (compactPosterior μ hc c Q : Measure E).support = (μ : Measure E).support := by
  exact Probability.support_tilted_eq _ (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop))
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
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
section CovarianceRadius
open ProbabilityTheory
/-- **Posterior covariance radius bound**: if the prior support lies in the closed ball of radius `r`, then
`‖Cov μ_{c,Q}‖ ≤ r²` for every finite `(c, Q)`. Route: `⟪A v, w⟫ = cov(⟪v,·⟫, ⟪w,·⟫)`, Cauchy–Schwarz,
`Var⟪v,·⟫ ≤ ∫ ⟪v,x⟫² ≤ r² ‖v‖²` on the support, then `‖A v‖² = ⟪A v, A v⟫ ≤ r² ‖v‖ ‖A v‖`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure E).support ⊆ Metric.closedBall (0 : E) r) (c : E) (Q : E →L[ℝ] E) :
    ‖FunctionalInequalities.Covariance.operator (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E)‖ ≤ r ^ 2 := by
    let ν : Measure E := FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q
    let A : E →L[ℝ] E := FunctionalInequalities.Covariance.operator ν
    have hprob : IsProbabilityMeasure ν := by
      dsimp [ν]
      infer_instance
    change ‖A‖ ≤ r ^ 2

    have hid : MemLp id 2 ν := by
      simpa only [ν] using FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two μ hc c Q

    have hmem (v : E) :
        MemLp (fun x : E => ⟪v, x⟫) 2 ν := by
      have hh : MemLp (fun x : E => ⟪id x, v⟫) 2 ν :=
        hid.inner_const v
      simpa [real_inner_comm] using hh

    have hvar (v : E) :
        variance (fun x : E => ⟪v, x⟫) ν ≤ r ^ 2 * ‖v‖ ^ 2 := by
      have hle :
          (∫ x, (⟪v, x⟫) ^ 2 ∂ν) ≤
            ∫ _x, r ^ 2 * ‖v‖ ^ 2 ∂ν := by
        apply integral_mono_ae
        · exact (hmem v).integrable_sq
        · exact integrable_const _
        · filter_upwards [Measure.support_mem_ae (μ := ν)] with x hx
          have hx' : x ∈ (μ : Measure E).support := by
            rw [← FunctionalInequalities.Probability.Posterior.compactPosterior_support μ hc c Q]
            exact hx
          have hxball : x ∈ Metric.closedBall (0 : E) r :=
            hsupp hx'
          have hnorm : ‖x‖ ≤ r := by
            simpa [mem_closedBall_zero_iff] using hxball
          have habs : |⟪v, x⟫| ≤ r * ‖v‖ := by
            calc
              |⟪v, x⟫| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
              _ ≤ ‖v‖ * r :=
                mul_le_mul_of_nonneg_left hnorm (norm_nonneg v)
              _ = r * ‖v‖ := by ring
          have hsquare : ⟪v, x⟫ ^ 2 ≤ (r * ‖v‖) ^ 2 := by
            rw [← sq_abs]
            nlinarith [habs, abs_nonneg ⟪v, x⟫,
              mul_self_nonneg (r * ‖v‖ - |⟪v, x⟫|)]
          calc
            ⟪v, x⟫ ^ 2 ≤ (r * ‖v‖) ^ 2 := hsquare
            _ = r ^ 2 * ‖v‖ ^ 2 := by ring
      have hv :=
        variance_le_expectation_sq
          (μ := ν) (X := fun x : E => ⟪v, x⟫)
          (hmem v).aestronglyMeasurable
      have hv' :
          variance (fun x : E => ⟪v, x⟫) ν ≤
            ∫ x, (⟪v, x⟫) ^ 2 ∂ν := by
        simpa only [Pi.pow_apply] using hv
      calc
        variance (fun x : E => ⟪v, x⟫) ν ≤
            ∫ x, (⟪v, x⟫) ^ 2 ∂ν := hv'
        _ ≤ ∫ _x, r ^ 2 * ‖v‖ ^ 2 ∂ν := hle
        _ = r ^ 2 * ‖v‖ ^ 2 := by simp

    have hcov (v w : E) :
        |⟪A v, w⟫| ≤ r ^ 2 * ‖v‖ * ‖w‖ := by
      have hcs :=
        FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_readable
          (hmem v) (hmem w)
      have hsq :
          |⟪A v, w⟫| ^ 2 ≤
            (r ^ 2 * ‖v‖ * ‖w‖) ^ 2 := by
        rw [FunctionalInequalities.Covariance.operator_inner]
        rw [covarianceBilin_apply_eq_cov
          (FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two μ hc c Q)]
        calc
          |covariance (fun x : E => ⟪v, x⟫)
              (fun x : E => ⟪w, x⟫) ν| ^ 2
              = covariance (fun x : E => ⟪v, x⟫)
                  (fun x : E => ⟪w, x⟫) ν ^ 2 := by
                    rw [sq_abs]
          _ ≤ variance (fun x : E => ⟪v, x⟫) ν *
                variance (fun x : E => ⟪w, x⟫) ν := hcs
          _ ≤ (r ^ 2 * ‖v‖ ^ 2) * (r ^ 2 * ‖w‖ ^ 2) := by
            exact mul_le_mul (hvar v) (hvar w)
              (variance_nonneg _ _) (by positivity)
          _ = (r ^ 2 * ‖v‖ * ‖w‖) ^ 2 := by ring
      have hnonneg : 0 ≤ r ^ 2 * ‖v‖ * ‖w‖ := by positivity
      by_contra h
      have hlt : r ^ 2 * ‖v‖ * ‖w‖ < |⟪A v, w⟫| :=
        lt_of_not_ge h
      nlinarith [hsq, abs_nonneg ⟪A v, w⟫]

    apply ContinuousLinearMap.opNorm_le_bound A
    · exact pow_nonneg hr 2
    · intro v
      have hsq : ‖A v‖ ^ 2 ≤ r ^ 2 * ‖v‖ * ‖A v‖ := by
        calc
          ‖A v‖ ^ 2 = ⟪A v, A v⟫ := by
            symm
            exact real_inner_self_eq_norm_sq _
          _ ≤ |⟪A v, A v⟫| := le_abs_self _
          _ ≤ r ^ 2 * ‖v‖ * ‖A v‖ := hcov v (A v)
      by_cases hz : ‖A v‖ = 0
      · simp [hz]
        positivity
      · have hpos : 0 < ‖A v‖ := norm_pos_iff.mpr (by
          intro hav
          apply hz
          simp [hav])
        nlinarith
