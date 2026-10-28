-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_one_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:37:47.993932+00:00
-- url     : https://prove2.me/submissions/0aebae64-9503-4dcc-a07b-77e9d76d0b9f

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Base
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_continuous_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_dynkin_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integrable_integral_of_ae_bound_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_inner_cov_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBoundCompact_two_of_letwinCompact_readable
import Theorems.Thm_FunctionalInequalities_KLS_compactPosterior_cumulant_bound_readable
import Theorems.Thm_FunctionalInequalities_KLS_opNorm_covariance_compactPosterior_le_sq_radius_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorCovariance_joint_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantEnergy_one_is_one_readable

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
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem FunctionalInequalities.Probability.integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))
end
section
open FunctionalInequalities.Probability
/-- The ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support. -/
theorem FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {w : E} (hw : w ∈ (affineSupport μ).directionᗮ) :
    operator (μ : Measure E) w = 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [operator_inner, inner_zero_left, covarianceBilin_apply hμ]
  have hm : (∫ x, id x ∂(μ : Measure E)) ∈ affineSupport μ := integral_id_mem_affineSupport μ hμ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_mem_affineSupport μ] with z hz
  have hdir : z - ∫ x, id x ∂(μ : Measure E) ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hz hm
  show inner ℝ w (z - ∫ x, id x ∂(μ : Measure E)) * inner ℝ y (z - ∫ x, id x ∂(μ : Measure E)) = 0
  rw [Submodule.inner_left_of_mem_orthogonal hdir hw, zero_mul]
end
end
end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An injective covariance operator forces full affine support. -/
theorem FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hinj : Function.Injective (Covariance.operator (μ : Measure E))) :
    Probability.affineSupport μ = ⊤ := by
  have hperp : (Probability.affineSupport μ).directionᗮ = ⊥ := by
    apply bot_unique
    intro w hw
    have h := Covariance.operator_apply_eq_zero_of_mem_orthogonal μ h2 hw
    have hz : w = 0 := hinj (h.trans (map_zero _).symm)
    simpa only [Submodule.mem_bot] using hz
  have hdir : (Probability.affineSupport μ).direction = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hne : (Probability.affineSupport μ : Set E).Nonempty :=
    ⟨Probability.origin μ, (Probability.origin μ).property⟩
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
/-- The covariance operator is self-adjoint. -/
theorem FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E) : IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _
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
/-- The posterior has the same affine support as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_affineSupport (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    Probability.affineSupport (compactPosterior μ hc c Q) = Probability.affineSupport μ := by
  unfold Probability.affineSupport
  rw [compactPosterior_support]
/-- The posterior has finite second moment. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    MemLp id 2 (compactPosterior μ hc c Q : Measure E) := by
  change MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q))
  have hn : MemLp (fun x : E => ‖x‖) 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q continuous_norm
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
/-- At the initial parameters the posterior is the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_zero (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) : compactPosterior μ hc 0 0 = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change (μ : Measure E).tilted (quadraticExponent (0 : E) 0) = _
  have he : quadraticExponent (0 : E) (0 : E →L[ℝ] E) = 0 := by funext x; simp [quadraticExponent]
  rw [he, tilted_zero]
/-- For a prior with full affine support every posterior has strictly positive covariance. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_covariance_pos_of_affineSupport_eq_top (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hfull : Probability.affineSupport μ = ⊤)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ := by
  apply Covariance.inner_operator_self_pos_of_affineSupport_eq_top_readable (compactPosterior μ hc c Q)
    (compactPosterior_memLp_id_two μ hc c Q) ?_ hv
  rw [compactPosterior_affineSupport, hfull]
end
end
end

section
open MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An isotropic law has full affine support. -/
theorem FunctionalInequalities.KLS.Isotropic.affineSupport_eq_top {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ := by
  apply Probability.affineSupport_eq_top_of_covariance_injective μ hiso.memLp_two
  rw [hiso.covariance_identity]
  exact fun _ _ h => h
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- For a compactly supported isotropic prior every posterior has strictly positive covariance. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_pos (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ :=
  compactPosterior_covariance_pos_of_affineSupport_eq_top μ hc (hiso.affineSupport_eq_top) c Q hv
/-- The posterior covariance is a positive operator. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    (Covariance.operator (compactPosterior μ hc c Q : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv).le
variable {ι : Type*} [Fintype ι]
end
end
end

section
noncomputable section
open scoped NNReal
section Cutoff
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
theorem FunctionalInequalities.Probability.Diffusion.ballCutoff_mem_Icc (R : ℝ) (p : V) : ballCutoff R p ∈ Set.Icc (0 : ℝ) 1 := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
theorem FunctionalInequalities.Probability.Diffusion.lipschitzWith_ballCutoff (R : ℝ) : LipschitzWith 1 (ballCutoff (V := V) R) := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have hn : LipschitzWith 1 (fun x : V => ‖x‖) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        abs_norm_sub_norm_le x y
  change LipschitzWith 1 (fun p : V => max 0 (min 1 (R + 1 - ‖p‖)))
  simpa only [zero_add, max_eq_right (show (0 : ℝ≥0) ≤ 1 by positivity)] using
    (LipschitzWith.const (0 : ℝ)).max
      ((LipschitzWith.const (1 : ℝ)).min ((LipschitzWith.const (R + 1)).sub hn))
theorem FunctionalInequalities.Probability.Diffusion.hasCompactSupport_ballCutoff (R : ℝ) : HasCompactSupport (ballCutoff (V := V) R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V) (R + 1))
  intro x hx
  have hr : R + 1 ≤ ‖x‖ :=
    le_of_lt (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
  exact max_eq_left (le_trans (min_le_right _ _) (sub_nonpos.mpr hr))
end Cutoff
end
end

section
noncomputable section
open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
theorem FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff (R : ℝ) : IsCutoff (ballCutoff (V := Param n) R) :=
  { lipschitz := ⟨1, lipschitzWith_ballCutoff R⟩
    compactSupport := hasCompactSupport_ballCutoff R
    mem_Icc := fun p => ballCutoff_mem_Icc R p }
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
private theorem FunctionalInequalities.KLS.BKL.Localization.integral_le_of_nonneg_bound
    {α : Type*} [MeasurableSpace α] {M : Measure α} {f g : α → ℝ}
    (hg : Integrable g M)
    (hf : ∀ᵐ x ∂M, 0 ≤ f x)
    (hfg : ∀ᵐ x ∂M, f x ≤ g x) :
    ∫ x, f x ∂M ≤ ∫ x, g x ∂M := by
  by_cases hi : Integrable f M
  · exact integral_mono_ae hi hg hfg
  · rw [integral_undef hi]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hfg] with x hx hxy
    exact hx.trans hxy
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- **Base case `m = 2`** (BKL p. 25, "the case m = 2 follows from (78)"): under the compact Letwin bound and
`K ≥ 5`, `CutoffEnergyClaim K 1`. -/
theorem solution (hL : FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 5 ≤ K) :
    FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K 1 := by
  classical
  intro n μ hc hiso hLC u hu ε hε T hT
  refine ⟨0, ?_⟩
  intro R _hR Ω _ P _ W ℱ hW hℱ0 hnull p hp
  let F : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q => ⟪FunctionalInequalities.KLS.BKL.Localization.cov μ hc q u, u⟫
  let G : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q => FunctionalInequalities.Probability.Diffusion.ballCutoff R q ^ 2 * F q
  let H : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q =>
    FunctionalInequalities.Probability.Diffusion.ballCutoff R q ^ 2 *
      FunctionalInequalities.KLS.BKL.cumulantEnergy
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) 2 u
  have hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff (FunctionalInequalities.Probability.Diffusion.ballCutoff (V := FunctionalInequalities.KLS.BKL.Localization.Param n) R) :=
    FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff R
  have hcov : ContDiff ℝ 2 (FunctionalInequalities.KLS.BKL.Localization.cov μ hc) :=
    (FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint_readable μ hc).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hF : ContDiff ℝ 2 F := by
    have hh : ContDiff ℝ 2 (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => ⟪u, FunctionalInequalities.KLS.BKL.Localization.cov μ hc q u⟫) :=
      (innerSL ℝ u).contDiff.comp (hcov.clm_apply contDiff_const)
    simpa only [F, real_inner_comm] using hh
  have hFpos (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : 0 ≤ F q :=
    (FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive
      μ hc hiso q.1 q.2).inner_nonneg_left u
  have hGcont : Continuous G :=
    ((FunctionalInequalities.Probability.Diffusion.lipschitzWith_ballCutoff R).continuous.pow 2).mul hF.continuous
  have hGpos (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : 0 ≤ G q :=
    mul_nonneg (sq_nonneg _) (hFpos q)
  have hHpos (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : 0 ≤ H q := by
    dsimp only [H, FunctionalInequalities.KLS.BKL.cumulantEnergy]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  obtain ⟨r, hr⟩ :=
    hc.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  let r' : ℝ := max r 0
  have hr' : 0 ≤ r' := le_max_right _ _
  have hrsupp :
      (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r' := by
    intro x hx
    have hxnorm : ‖x‖ ≤ r := by
      simpa only [mem_closedBall_zero_iff] using hr hx
    simpa only [mem_closedBall_zero_iff] using
      hxnorm.trans (le_max_left r 0)
  have hFbound (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : F q ≤ r' ^ 2 := by
    have hnorm : ‖FunctionalInequalities.KLS.BKL.Localization.cov μ hc q u‖ ≤ ‖FunctionalInequalities.KLS.BKL.Localization.cov μ hc q‖ := by
      simpa only [hu, mul_one] using (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q).le_opNorm u
    calc
      F q ≤ ‖FunctionalInequalities.KLS.BKL.Localization.cov μ hc q u‖ * ‖u‖ := real_inner_le_norm _ _
      _ = ‖FunctionalInequalities.KLS.BKL.Localization.cov μ hc q u‖ := by rw [hu, mul_one]
      _ ≤ ‖FunctionalInequalities.KLS.BKL.Localization.cov μ hc q‖ := hnorm
      _ ≤ r' ^ 2 :=
        FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius_readable
          μ hc hr' hrsupp q.1 q.2
  have hGbound (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : G q ≤ r' ^ 2 := by
    have hg := FunctionalInequalities.Probability.Diffusion.ballCutoff_mem_Icc R q
    have hsq : FunctionalInequalities.Probability.Diffusion.ballCutoff R q ^ 2 ≤ 1 := by
      nlinarith [hg.1, hg.2]
    calc
      G q ≤ 1 * (r' ^ 2) :=
        mul_le_mul hsq (hFbound q) (hFpos q) zero_le_one
      _ = r' ^ 2 := one_mul _
  have hB :
      ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |8 * G (p s ω)| ≤ 8 * r' ^ 2 := by
    filter_upwards [] with ω
    intro s _hs
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (hGpos _))]
    exact mul_le_mul_of_nonneg_left (hGbound _) (by norm_num)
  have hupperInt :
      Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, 8 * G (p s ω)) P :=
    hp.integrable_integral_of_ae_bound_readable
      (continuous_const.mul hGcont) hB hT
  have h8 : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact 2 8 :=
    FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact_readable hL
  have hq :=
    FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_Q_posSemidef_readable (μ := μ) (hc := hc) hiso hγ hp
  have hbound :
      ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → H (p s ω) ≤ 8 * G (p s ω) := by
    filter_upwards [hq] with ω hω
    intro s hs
    have hcumul :=
      FunctionalInequalities.KLS.compactPosterior_cumulant_bound_readable μ hc hiso hLC
        (d := 2) (b := 8) (p s ω).1 (p s ω).2
        (hω s hs).1 (hω s hs).2 (by norm_num) h8 u
    calc
      H (p s ω) ≤ FunctionalInequalities.Probability.Diffusion.ballCutoff R (p s ω) ^ 2 * (8 * F (p s ω)) :=
        mul_le_mul_of_nonneg_left hcumul (sq_nonneg _)
      _ = 8 * G (p s ω) := by
        dsimp only [G]
        ring
  have hmono :
      (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, H (p s ω) ∂volume ∂P) ≤
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, 8 * G (p s ω) ∂volume ∂P := by
    apply FunctionalInequalities.KLS.BKL.Localization.integral_le_of_nonneg_bound hupperInt
    · exact Filter.Eventually.of_forall fun ω =>
        integral_nonneg fun s => hHpos (p s ω)
    · filter_upwards [hbound] with ω hω
      apply FunctionalInequalities.KLS.BKL.Localization.integral_le_of_nonneg_bound
        (((continuous_const.mul hGcont).comp (hp.continuous_readable ω)).integrableOn_Ioc)
      · exact Filter.Eventually.of_forall fun s => hHpos (p s ω)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hω s hs.1.le
  have hmono' :
      FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p 2 u T ≤
        8 * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, G (p s ω) ∂volume ∂P := by
    change
      (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, H (p s ω) ∂volume ∂P) ≤ _
    simpa only [integral_const_mul] using hmono
  have hdyn :=
    FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.dynkin_readable (μ := μ) (hc := hc) hiso hγ hℱ0 hnull hp hF hT
  have hgenq (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : FunctionalInequalities.KLS.BKL.Localization.generator μ hc F q = -F q :=
    FunctionalInequalities.KLS.BKL.Localization.generator_inner_cov_readable μ hc hiso q u u
  have hgen :
      (∫ ω, F (p T ω) ∂P) - F 0 =
        -(∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, G (p s ω) ∂volume ∂P) := by
    simpa only [hgenq, mul_neg, integral_neg] using hdyn.2
  have hinit : F 0 = 1 := by
    change
      ⟪FunctionalInequalities.Covariance.operator
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc 0 0 : Measure (EuclideanSpace ℝ (Fin n))) u, u⟫ = 1
    rw [FunctionalInequalities.Probability.Posterior.compactPosterior_zero, hiso.covariance_identity]
    change ⟪u, u⟫ = 1
    rw [real_inner_self_eq_norm_mul_norm, hu]
    norm_num
  have hEF : 0 ≤ ∫ ω, F (p T ω) ∂P :=
    integral_nonneg fun ω => hFpos (p T ω)
  have hupper :
      FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p 2 u T ≤ 8 := by
    linarith [hmono', hgen, hinit, hEF]
  have hzero := FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_one_is_one_readable μ hc hiso u hu
  change
    FunctionalInequalities.KLS.BKL.cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) 1 u +
        (1 / 2 : ℝ) * FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p 2 u T ≤
      FunctionalInequalities.KLS.BKL.envelope K 2 + ε
  rw [hzero]
  have henvelope : FunctionalInequalities.KLS.BKL.envelope K 2 = K := by simp [FunctionalInequalities.KLS.BKL.envelope]
  rw [henvelope]
  linarith
