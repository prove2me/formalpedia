-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.exists_cumulantEnergy_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:55.721755+00:00
-- url     : https://prove2.me/submissions/69db773d-d433-4468-b2b3-0cad1456f446

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_norm_posteriorMean_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_exists_sum_sq_cumulant_le_isotropic_readable
import Theorems.Thm_FunctionalInequalities_KLS_opNorm_covariance_compactPosterior_le_sq_radius_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_posterior_energy_transfer_readable

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
end
end
end

section
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
variable {ι : Type*} [Fintype ι]
end Mean
end
end

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}
variable (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- A-priori bound on the cumulant energies along the localization. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hLC : FunctionalInequalities.KLS.LogConcave μ) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
      ∀ u : EuclideanSpace ℝ (Fin n),
        FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C * ‖u‖ ^ 2 := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨r ^ 2, sq_nonneg r, ?_⟩
    intro p _ _ u
    let π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2
    have hπcompact : IsCompact (π : Measure (EuclideanSpace ℝ (Fin n))).support := by
      change IsCompact (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))).support
      rw [FunctionalInequalities.Probability.Posterior.compactPosterior_support]
      exact hc
    have hfirst (v : Fin 1 → EuclideanSpace ℝ (Fin n)) :
        FunctionalInequalities.Analysis.BakryEmery.cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) 1 v =
          ⟪v 0, FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2⟫ := by
      rw [FunctionalInequalities.Analysis.BakryEmery.cumulant, iteratedFDeriv_one_apply,
        ← FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_readable
          (π : Measure (EuclideanSpace ℝ (Fin n)))
          (fun t => FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hπcompact t) (v 0) 0]
      have hzero :
          (fun x : EuclideanSpace ℝ (Fin n) => ⟪(0 : EuclideanSpace ℝ (Fin n)), x⟫) = 0 := by
        funext x
        simp
      rw [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt, hzero, tilted_zero]
      exact FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean μ hc p.1 p.2 (v 0)
    have habs : |⟪u, FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2⟫| ≤ ‖u‖ * r :=
      (abs_real_inner_le_norm u _).trans
        (mul_le_mul_of_nonneg_left (FunctionalInequalities.KLS.BKL.Localization.norm_posteriorMean_le_readable μ hr hsupp p) (norm_nonneg u))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg u) hr)).2 habs
    have he :
        FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 0 u =
          ⟪u, FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2⟫ ^ 2 := by
      change (∑ J : Fin 0 → Fin n,
        FunctionalInequalities.Analysis.BakryEmery.cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) 1
          (Fin.cons u fun k => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (π : Measure (EuclideanSpace ℝ (Fin n))))
            (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2) = _
      simp only [hfirst, Fin.cons_zero]
      simp
    rw [he]
    simpa only [sq_abs, mul_pow, mul_comm] using hsq
  · obtain ⟨b, hb, hbound⟩ := FunctionalInequalities.KLS.BKL.exists_sum_sq_cumulant_le_isotropic_readable (n := n) d
    refine ⟨b * r ^ 2, mul_nonneg hb (sq_nonneg r), ?_⟩
    intro p hSym hQ u
    have htransfer := FunctionalInequalities.KLS.BKL.Localization.posterior_energy_transfer_readable μ hc hiso hLC p.1 p.2 hSym hQ
      (by omega : 1 ≤ d) hbound u
    let A := FunctionalInequalities.Covariance.operator
      (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
    have hA : ‖A‖ ≤ r ^ 2 :=
      FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius_readable μ hc hr hsupp p.1 p.2
    have hinner : ⟪A u, u⟫ ≤ r ^ 2 * ‖u‖ ^ 2 := by
      calc
        ⟪A u, u⟫ ≤ ‖A u‖ * ‖u‖ := real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg u)
        _ ≤ (r ^ 2 * ‖u‖) * ‖u‖ := by
          gcongr
        _ = r ^ 2 * ‖u‖ ^ 2 := by ring
    calc
      _ ≤ b * ⟪A u, u⟫ := htransfer
      _ ≤ b * (r ^ 2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hinner hb
      _ = (b * r ^ 2) * ‖u‖ ^ 2 := by ring
