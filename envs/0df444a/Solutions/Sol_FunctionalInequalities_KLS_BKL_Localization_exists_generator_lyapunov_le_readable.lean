-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.exists_generator_lyapunov_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:24.101706+00:00
-- url     : https://prove2.me/submissions/0d029dd0-9a5e-454c-a826-f4fe6d82db6a

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Positive
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound
import Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_comp_eq_id_readable
import Theorems.Thm_FunctionalInequalities_Analysis_opNorm_sq_le_hsNormSq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_sum_inner_apply_le_sqrt_hsNormSq_mul_readable
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_hsNormSq_snd_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_norm_sq_fst_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_stdTrace_ringInverse_cov_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_norm_posteriorMean_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_sq_fderiv_stdTrace_ringInverse_cov_noise_le_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_mul_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorCovariance_joint_readable

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
open scoped RealInnerProductSpace
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- A strictly positive operator (`⟪T v, v⟫ > 0` for `v ≠ 0`) on a finite-dimensional space is a unit. -/
theorem FunctionalInequalities.Analysis.isUnit_of_inner_self_pos (T : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫) : IsUnit T := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot T.toLinearMap).mpr
  apply bot_unique
  intro v hv
  have hv' : T v = 0 := hv
  change v = 0
  by_contra hne
  have hp := hpos v hne
  rw [hv', inner_zero_left] at hp
  exact (lt_irrefl 0) hp
end FiniteDimensional
section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A right inverse of a self-adjoint operator is self-adjoint. -/
theorem FunctionalInequalities.Analysis.isSelfAdjoint_of_comp_eq_id [CompleteSpace E] (T B : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hTB : T.comp B = ContinuousLinearMap.id ℝ E) : IsSelfAdjoint B := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hf (z : E) : T (B z) = z := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : E →L[ℝ] E => L z) hTB
  have hh := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) (B x) (B y)
  change ⟪T (B x), B y⟫ = ⟪B x, T (B y)⟫ at hh
  rw [hf, hf] at hh
  exact hh.symm
end General
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
/-- The posterior covariance is a unit. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    IsUnit (Covariance.operator (compactPosterior μ hc c Q : Measure E)) :=
  Analysis.isUnit_of_inner_self_pos _ (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)
/-- The canonical inverse `Ring.inverse (Cov μ_{c,Q})` is a two-sided, self-adjoint, strictly positive inverse. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_ringInverse_covariance (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ E ∧
    (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ E ∧
    IsSelfAdjoint (Ring.inverse A) ∧
    (∀ v : E, v ≠ 0 → 0 < ⟪Ring.inverse A v, v⟫) := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hu : IsUnit A := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hright : A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ E :=
    Ring.mul_inverse_cancel A hu
  have hleft : (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ E :=
    Ring.inverse_mul_cancel A hu
  exact ⟨hright, hleft, Analysis.isSelfAdjoint_of_comp_eq_id A _ (Covariance.operator_isSelfAdjoint _) hright,
    fun v hv => Analysis.inner_self_pos_of_comp_eq_id_readable A _
      (fun w hw => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hw) hright hv⟩
variable {ι : Type*} [Fintype ι]
end
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
section JointCoefficients
/-- **Joint smoothness of the rate** `A⁻¹ = Cov(μ_{c,Q})⁻¹` of (67): isotropy makes the posterior covariance a
unit at every finite `(c, Q)`, and the Banach-algebra inverse is analytic there. -/
theorem FunctionalInequalities.KLS.Isotropic.contDiff_ringInverse_covariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hs := (contDiff_posteriorCovariance_joint_readable μ hc).contDiffAt (x := p)
  obtain ⟨u, hu⟩ := Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hi : ContDiffAt ℝ ∞ Ring.inverse
      (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hi.comp p hs
end JointCoefficients
end
end
end

section
noncomputable section
open scoped RealInnerProductSpace
section
variable {n : ℕ}
private theorem FunctionalInequalities.Analysis.positive_inner_sq_le
    {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hM : M.IsPositive) (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, M v⟫ ^ 2 ≤ ⟪u, M u⟫ * ⟪v, M v⟫ := by
  have hsym : ⟪v, M u⟫ = ⟪u, M v⟫ := by
    calc
      ⟪v, M u⟫ = ⟪M u, v⟫ := (real_inner_comm v (M u)).symm
      _ = ⟪u, M v⟫ := hM.isSymmetric u v
  have hquad :
      ∀ t : ℝ, 0 ≤ ⟪u, M u⟫ * (t * t) + (2 * ⟪u, M v⟫) * t +
        ⟪v, M v⟫ := by
    intro t
    have hp := hM.inner_nonneg_right (t • u + v)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right] at hp
    rw [hsym] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]
theorem FunctionalInequalities.Analysis.hsNormSq_nonneg (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : 0 ≤ hsNormSq M := by
  unfold hsNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
/-- The trace of a positive operator is nonnegative. -/
theorem FunctionalInequalities.Analysis.stdTrace_nonneg {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} (hM : M.IsPositive) :
    0 ≤ stdTrace M := by
  unfold stdTrace
  exact Finset.sum_nonneg fun i _ =>
    hM.inner_nonneg_right (EuclideanSpace.basisFun (Fin n) ℝ i)
/-- For a positive operator, `‖M‖²_HS ≤ (tr M)²` (Cauchy–Schwarz for the semi-inner product `⟪M·,·⟫`). -/
theorem FunctionalInequalities.Analysis.hsNormSq_le_stdTrace_sq {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hM : M.IsPositive) : hsNormSq M ≤ stdTrace M ^ 2 := by
  unfold hsNormSq stdTrace
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact positive_inner_sq_le hM
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
end
end
end

noncomputable section
section S5E1BLyapunovBound
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
private theorem FunctionalInequalities.KLS.BKL.Localization.ringInverse_isPositive (hiso : KLS.Isotropic μ) (p : Param n) :
    (Ring.inverse (cov μ hc p)).IsPositive := by
  have hs :=
    Isotropic.compactPosterior_ringInverse_covariance μ hc hiso p.1 p.2
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hs.2.2.1, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    change 0 ≤
      ⟪Ring.inverse (cov μ hc p) (0 : EuclideanSpace ℝ (Fin n)),
        (0 : EuclideanSpace ℝ (Fin n))⟫
    simp
  · exact (hs.2.2.2 v hv).le
section NormedSpace
variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_add_local {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    diffusionGenerator b σ (fun y => u y + v y) x =
      diffusionGenerator b σ u x + diffusionGenerator b σ v x := by
  have hu' : DifferentiableAt ℝ u x :=
    hu.differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x :=
    hv.differentiableAt (by norm_num)
  have hfu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond (a c : V) :
      fderiv ℝ (fderiv ℝ (fun y => u y + v y)) x a c =
        fderiv ℝ (fderiv ℝ u) x a c +
          fderiv ℝ (fderiv ℝ v) x a c := by
    have h :
        (fun y => fderiv ℝ (fun z => u z + v z) y) =ᶠ[nhds x]
          (fun y => fderiv ℝ u y + fderiv ℝ v y) := by
      filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hyu hyv
      rw [fderiv_fun_add (hyu.differentiableAt (by norm_num))
        (hyv.differentiableAt (by norm_num))]
    rw [h.fderiv_eq, fderiv_fun_add hfu hfv]
    simp only [add_apply]
  unfold diffusionGenerator
  rw [fderiv_fun_add hu' hv']
  simp_rw [hsecond]
  simp only [add_apply, Finset.sum_add_distrib]
  ring
private theorem FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_const_local {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) (c : ℝ) (x : V) :
    diffusionGenerator b σ (fun _ : V => c) x = 0 := by
  unfold diffusionGenerator
  change
    (fderiv ℝ (Function.const V c) x) (b x) +
        1 / 2 * ∑ k,
          ((fderiv ℝ (fderiv ℝ (Function.const V c)) x) (σ x k)) (σ x k) = 0
  simp
end NormedSpace
set_option maxHeartbeats 1000000 in
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (h8 : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc) p ≤ K * FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc p := by
  let K : ℝ := 1 + r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · intro p hSym hQ
    let R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p)
    let G : ℝ := FunctionalInequalities.Analysis.stdTrace R
    have hRpos : R.IsPositive := by
      simpa [R] using FunctionalInequalities.KLS.BKL.Localization.ringInverse_isPositive μ hc hiso p
    have hG : 0 ≤ G := by
      simpa [G] using FunctionalInequalities.Analysis.stdTrace_nonneg hRpos
    have hmean : ‖FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2‖ ≤ r :=
      FunctionalInequalities.KLS.BKL.Localization.norm_posteriorMean_le_readable μ hr hsupp p
    have hop : ‖R‖ ^ 2 ≤ G ^ 2 := by
      have h1 := FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq_readable R
      have h2 := FunctionalInequalities.Analysis.hsNormSq_le_stdTrace_sq hRpos
      simpa [G] using le_trans h1 h2
    have hRnorm : ‖R‖ ≤ G :=
      (sq_le_sq₀ (norm_nonneg _) hG).mp hop
    have hRa : ‖R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)‖ ≤ ‖R‖ * r := by
      calc
        ‖R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)‖ ≤
            ‖R‖ * ‖FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2‖ :=
          R.le_opNorm _
        _ ≤ ‖R‖ * r :=
          mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
    have hRG : ‖R‖ * r ≤ r * G := by
      calc
        ‖R‖ * r = r * ‖R‖ := by ring
        _ ≤ r * G := mul_le_mul_of_nonneg_left hRnorm hr
    have hfst :
        2 * ⟪p.1, R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)⟫ ≤
          ‖p.1‖ ^ 2 + r ^ 2 * G ^ 2 := by
      have hi :
          ⟪p.1, R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)⟫ ≤
            ‖p.1‖ * ‖R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)‖ :=
        real_inner_le_norm _ _
      have h₁ :
          2 * ⟪p.1, R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)⟫ ≤
            2 * (‖p.1‖ * ‖R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)‖) :=
        mul_le_mul_of_nonneg_left hi (by norm_num)
      have h₂ :
          2 * (‖p.1‖ * ‖R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)‖) ≤
            2 * (‖p.1‖ * (‖R‖ * r)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRa (norm_nonneg _)) (by norm_num)
      have h₃ :
          2 * (‖p.1‖ * (‖R‖ * r)) ≤
            2 * (‖p.1‖ * (r * G)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRG (norm_nonneg _)) (by norm_num)
      calc
        2 * ⟪p.1, R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)⟫ ≤
            2 * (‖p.1‖ * ‖R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)‖) := h₁
        _ ≤ 2 * (‖p.1‖ * (‖R‖ * r)) := h₂
        _ ≤ 2 * (‖p.1‖ * (r * G)) := h₃
        _ ≤ ‖p.1‖ ^ 2 + (r * G) ^ 2 := by
          simpa only [mul_assoc] using two_mul_le_add_sq ‖p.1‖ (r * G)
        _ = ‖p.1‖ ^ 2 + r ^ 2 * G ^ 2 := by ring
    have hq :
        2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
          R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
          FunctionalInequalities.Analysis.hsNormSq p.2 + G ^ 2 := by
      have hcs := FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul_readable p.2 R
      have hsR : FunctionalInequalities.Analysis.hsNormSq R ≤ G ^ 2 :=
        FunctionalInequalities.Analysis.hsNormSq_le_stdTrace_sq hRpos
      have hsqrtR : Real.sqrt (FunctionalInequalities.Analysis.hsNormSq R) ≤ G := by
        calc
          Real.sqrt (FunctionalInequalities.Analysis.hsNormSq R) ≤ Real.sqrt (G ^ 2) :=
            Real.sqrt_le_sqrt hsR
          _ = G := by
            simpa [abs_of_nonneg hG] using Real.sqrt_sq_eq_abs G
      calc
        2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
            R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
            2 * (Real.sqrt (FunctionalInequalities.Analysis.hsNormSq p.2) * Real.sqrt (FunctionalInequalities.Analysis.hsNormSq R)) :=
          mul_le_mul_of_nonneg_left hcs (by norm_num)
        _ ≤ 2 * (Real.sqrt (FunctionalInequalities.Analysis.hsNormSq p.2) * G) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsqrtR (Real.sqrt_nonneg _)) (by norm_num)
        _ ≤ Real.sqrt (FunctionalInequalities.Analysis.hsNormSq p.2) ^ 2 + G ^ 2 := by
          simpa only [mul_assoc] using
            two_mul_le_add_sq (Real.sqrt (FunctionalInequalities.Analysis.hsNormSq p.2)) G
        _ = FunctionalInequalities.Analysis.hsNormSq p.2 + G ^ 2 := by
          rw [Real.sq_sqrt (FunctionalInequalities.Analysis.hsNormSq_nonneg p.2)]
    have hGgen :
        FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p ≤
          (1 + 8 * n) * G := by
      simpa [G, R] using
        FunctionalInequalities.KLS.BKL.Localization.generator_stdTrace_ringInverse_cov_le_readable μ hc hiso hLC h8 p hSym hQ
    have hGcarre :
        ∑ k, (fderiv ℝ
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p
          (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)) ^ 2 ≤
          8 * n * G ^ 2 := by
      simpa [G, R] using
        FunctionalInequalities.KLS.BKL.Localization.sum_sq_fderiv_stdTrace_ringInverse_cov_noise_le_readable μ hc hiso hLC h8 p hSym hQ
    have hC : ContDiff ℝ 2 (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => ‖q.1‖ ^ 2) := by
      have hf : ContDiff ℝ 2 (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => q.1) := contDiff_fst
      simpa only [real_inner_self_eq_norm_sq] using ContDiff.inner ℝ hf hf
    have hQdiff : ContDiff ℝ 2 (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.hsNormSq q.2) := by
      have hR : ContDiff ℝ ∞ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.hsNormSq q.2) := by
        unfold FunctionalInequalities.Analysis.hsNormSq
        apply ContDiff.sum
        intro i hi
        apply ContDiff.sum
        intro j hj
        exact
          (ContDiff.inner ℝ contDiff_const
            (contDiff_snd.clm_apply contDiff_const)).pow 2
      exact hR.of_le (WithTop.coe_le_coe.mpr le_top)
    have hGdiff :
        ContDiff ℝ 2
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) := by
      have hR :
          ContDiff ℝ ∞
            (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) :=
        FunctionalInequalities.KLS.Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
      have hT :
          ContDiff ℝ ∞
            (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) := by
        unfold FunctionalInequalities.Analysis.stdTrace
        apply ContDiff.sum
        intro i hi
        exact ContDiff.inner ℝ contDiff_const (hR.clm_apply contDiff_const)
      exact hT.of_le (WithTop.coe_le_coe.mpr le_top)
    have hOne : ContDiff ℝ 2 (fun _ : FunctionalInequalities.KLS.BKL.Localization.Param n => (1 : ℝ)) := contDiff_const
    have hdecomp :
        FunctionalInequalities.KLS.BKL.Localization.generator μ hc (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc) p =
          FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun _ : FunctionalInequalities.KLS.BKL.Localization.Param n => 1) p +
            FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => ‖q.1‖ ^ 2) p +
            FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.hsNormSq q.2) p +
            FunctionalInequalities.KLS.BKL.Localization.generator μ hc
              (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) ^ 2) p := by
      unfold FunctionalInequalities.KLS.BKL.Localization.generator FunctionalInequalities.KLS.BKL.Localization.lyapunov
      rw [FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_add_local
        (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
        ((hOne.add hC).add hQdiff).contDiffAt
        (hGdiff.pow 2).contDiffAt]
      rw [FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_add_local
        (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
        (hOne.add hC).contDiffAt hQdiff.contDiffAt]
      rw [FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_add_local
        (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
        hOne.contDiffAt hC.contDiffAt]
    have hsquare :
        FunctionalInequalities.KLS.BKL.Localization.generator μ hc
            (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) ^ 2) p ≤
          (2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
      have hmul :=
        FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul_readable (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) (x := p)
          hGdiff.contDiffAt hGdiff.contDiffAt
      have hfirst :
          2 * G *
              FunctionalInequalities.KLS.BKL.Localization.generator μ hc
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p ≤
            2 * (1 + 8 * n) * G ^ 2 := by
        have h :=
          mul_le_mul_of_nonneg_left hGgen (by positivity : 0 ≤ 2 * G)
        calc
          2 * G *
              FunctionalInequalities.KLS.BKL.Localization.generator μ hc
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p ≤
              2 * G * ((1 + 8 * n) * G) := h
          _ = 2 * (1 + 8 * n) * G ^ 2 := by ring
      change FunctionalInequalities.Probability.Diffusion.diffusionGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) ^ 2) p ≤ _
      rw [show
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) ^ 2) =
            (fun q => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) *
              FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) by
        funext q
        rw [pow_two]]
      rw [hmul]
      change
        G * FunctionalInequalities.KLS.BKL.Localization.generator μ hc
              (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p +
            G * FunctionalInequalities.KLS.BKL.Localization.generator μ hc
              (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p +
            ∑ k, (fderiv ℝ
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p
                (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)) *
              (fderiv ℝ
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p
                (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)) ≤ _
      calc
        _ = 2 * G *
              FunctionalInequalities.KLS.BKL.Localization.generator μ hc
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p +
              ∑ k, (fderiv ℝ
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p
                (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)) ^ 2 := by
          simp only [pow_two]
          ring
        _ ≤ 2 * (1 + 8 * n) * G ^ 2 + 8 * n * G ^ 2 :=
          add_le_add hfirst hGcarre
        _ = (2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by ring
    have hbound :
        FunctionalInequalities.KLS.BKL.Localization.generator μ hc (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc) p ≤
          ‖p.1‖ ^ 2 + FunctionalInequalities.Analysis.hsNormSq p.2 + 1 +
            (r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
      rw [hdecomp]
      rw [FunctionalInequalities.KLS.BKL.Localization.generator_norm_sq_fst_readable μ hc hiso p, FunctionalInequalities.KLS.BKL.Localization.generator_hsNormSq_snd_readable μ hc hiso p]
      have hconst : FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun _ : FunctionalInequalities.KLS.BKL.Localization.Param n => 1) p = 0 :=
        FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_const_local (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) 1 p
      rw [hconst]
      have hGle : G ≤ 1 + G ^ 2 := by
        nlinarith [sq_nonneg (G - 1)]
      calc
        0 +
              (2 * ⟪p.1, R (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)⟫ + G) +
              2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
                R (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ +
              FunctionalInequalities.KLS.BKL.Localization.generator μ hc
                (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) ^ 2) p ≤
            (‖p.1‖ ^ 2 + r ^ 2 * G ^ 2 + G) +
              (FunctionalInequalities.Analysis.hsNormSq p.2 + G ^ 2) +
              (2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
          linarith [hfst, hq, hsquare]
        _ ≤ ‖p.1‖ ^ 2 + FunctionalInequalities.Analysis.hsNormSq p.2 + 1 +
            (r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n) * G ^ 2 := by
          nlinarith
    have hK1 : 1 ≤ K := by
      dsimp [K]
      nlinarith [sq_nonneg r, Nat.cast_nonneg (α := ℝ) n]
    have hKB : r ^ 2 + 2 + 2 * (1 + 8 * n) + 8 * n ≤ K := by
      dsimp [K]
      linarith
    have hrest : 0 ≤ 1 + ‖p.1‖ ^ 2 + FunctionalInequalities.Analysis.hsNormSq p.2 := by
      have hq0 := FunctionalInequalities.Analysis.hsNormSq_nonneg p.2
      positivity
    have hdom := mul_le_mul_of_nonneg_right hK1 hrest
    have hdom₂ := mul_le_mul_of_nonneg_right hKB (sq_nonneg G)
    have hV :
        FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc p = 1 + ‖p.1‖ ^ 2 + FunctionalInequalities.Analysis.hsNormSq p.2 + G ^ 2 := rfl
    rw [hV]
    nlinarith only [hbound, hdom, hdom₂]
