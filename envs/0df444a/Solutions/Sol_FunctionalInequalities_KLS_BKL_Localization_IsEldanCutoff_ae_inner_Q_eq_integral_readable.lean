-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_inner_Q_eq_integral_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:31.29221+00:00
-- url     : https://prove2.me/submissions/41182704-6ac7-479a-abc5-e3371d418807

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
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffCoefficients_admissible_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_ae_linear_eq_integral_readable
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

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
section S5D2BEldanQPsd
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Process
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
/-- **The `Q`-component is a pathwise integral of the drift** (no noise acts on `Q` in (67)):
`⟪Q_t x, y⟫ = ∫₀ᵗ γ(p_s)² ⟪A(p_s)⁻¹ x, y⟫ ds` for all `t ≥ 0` and all `x, y`, almost surely. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ)
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ x y : EuclideanSpace ℝ (Fin n),
      ⟪(p t ω).2 x, y⟫ =
        ∫ s in Set.Ioc (0 : ℝ) t, γ (p s ω) ^ 2 * ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) x, y⟫ := by
  classical
  obtain ⟨⟨_, hKb, _⟩, ⟨B, hB⟩, _, _⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.cutoffCoefficients_admissible_readable μ hc hiso hγ
  let Φ := FunctionalInequalities.Probability.Diffusion.stateEquiv (FunctionalInequalities.KLS.BKL.Localization.Param n)
  have hb : Continuous (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ)) :=
    Φ.continuous.comp (hKb.continuous.comp Φ.symm.continuous)
  have hB' : ∀ z,
      ‖FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ) z‖ ≤
        ‖Φ.toContinuousLinearMap‖ * B := by
    intro z
    change ‖Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm z))‖ ≤
      ‖Φ.toContinuousLinearMap‖ * B
    calc
      ‖Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm z))‖
          ≤ ‖Φ.toContinuousLinearMap‖ *
              ‖FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm z)‖ :=
        Φ.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖Φ.toContinuousLinearMap‖ * B :=
        mul_le_mul_of_nonneg_left (hB (Φ.symm z)).1 (norm_nonneg _)
  have hdiff :
      FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW
        (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ))
        (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ))
        (Φ 0) (fun t ω => Φ (p t ω)) := h
  have hfixed (x y : EuclideanSpace ℝ (Fin n)) :
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
        ⟪(p t ω).2 x, y⟫ =
          ∫ s in Set.Ioc (0 : ℝ) t,
            γ (p s ω) ^ 2 * ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) x, y⟫ := by
    let L : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] ℝ :=
      (innerSL ℝ y).comp
        ((ContinuousLinearMap.apply ℝ _ x).comp
          (ContinuousLinearMap.snd ℝ _ _))
    let L' : (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) →L[ℝ] ℝ :=
      L.comp Φ.symm.toContinuousLinearMap
    have hcoord (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : L' (Φ q) = ⟪q.2 x, y⟫ := by
      change ⟪y, (Φ.symm (Φ q)).2 x⟫ = ⟪q.2 x, y⟫
      rw [Φ.symm_apply_apply]
      exact real_inner_comm _ _
    have hL : ∀ z k,
        L' (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ) z k) = 0 := by
      intro z k
      change L' (Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ (Φ.symm z) k)) = 0
      rw [hcoord]
      change ⟪γ (Φ.symm z) • (0 : EuclideanSpace ℝ (Fin n)), y⟫ = 0
      rw [real_inner_smul_left, inner_zero_left, mul_zero]
    have hinit : L' (Φ 0) = 0 := by
      rw [hcoord]
      change ⟪(0 : EuclideanSpace ℝ (Fin n)), y⟫ = 0
      exact inner_zero_left _
    have hdrift (q : FunctionalInequalities.KLS.BKL.Localization.Param n) :
        L' (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ) (Φ q)) =
          γ q ^ 2 * ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q) x, y⟫ := by
      change L' (Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm (Φ q)))) = _
      rw [Φ.symm_apply_apply, hcoord]
      change ⟪(γ q ^ 2 • Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) x, y⟫ = _
      rw [smul_apply, real_inner_smul_left]
    have ha := FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral_readable hb hB' hdiff L' hL
    filter_upwards [ha] with ω hω
    intro t ht
    have he := hω t ht
    rw [hinit, zero_add, hcoord] at he
    simpa only [hdrift] using he
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hbasis :
      ∀ᵐ ω ∂P, ∀ i j : Fin n, ∀ t : ℝ, 0 ≤ t →
        ⟪(p t ω).2 (b i), b j⟫ =
          ∫ s in Set.Ioc (0 : ℝ) t,
            γ (p s ω) ^ 2 *
              ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫ := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact hfixed (b i) (b j)
  filter_upwards [hbasis] with ω hω
  intro t ht x y
  let ax : Fin n → ℝ := fun i => (b.repr x).ofLp i
  let ay : Fin n → ℝ := fun j => (b.repr y).ofLp j
  have hx : ∑ i, ax i • b i = x := b.sum_repr x
  have hy : ∑ j, ay j • b j = y := b.sum_repr y
  have hexpand (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      ⟪T x, y⟫ = ∑ i, ∑ j, ax i * ay j * ⟪T (b i), b j⟫ := by
    calc
      ⟪T x, y⟫ = ⟪T (∑ i, ax i • b i), ∑ j, ay j • b j⟫ := by
        rw [hx, hy]
      _ = ∑ i, ∑ j, ax i * ay j * ⟪T (b i), b j⟫ := by
        simp only [map_sum, map_smul, sum_inner, inner_sum,
          real_inner_smul_left, real_inner_smul_right, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hp : Continuous (fun s : ℝ => p s ω) := by
    obtain ⟨_, _, _, hv⟩ := hdiff
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      Φ.symm.continuous.comp (hv.continuous_path ω)
  obtain ⟨_, hγL⟩ := hγ.lipschitz
  have hg : Continuous (fun s : ℝ => γ (p s ω)) :=
    hγL.continuous.comp hp
  have hi : Continuous (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) := by
    simpa only [FunctionalInequalities.KLS.BKL.Localization.cov] using
      (FunctionalInequalities.KLS.Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).continuous
  have hcont (i j : Fin n) :
      Continuous fun s : ℝ =>
        γ (p s ω) ^ 2 *
          ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫ :=
    (hg.pow 2).mul
      (((hi.comp hp).clm_apply continuous_const).inner continuous_const)
  have hint (i j : Fin n) :
      IntegrableOn
        (fun s : ℝ =>
          γ (p s ω) ^ 2 *
            ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫)
        (Set.Ioc (0 : ℝ) t) volume :=
    (hcont i j).integrableOn_Ioc
  have hsum_cont (i : Fin n) :
      Continuous (fun s : ℝ =>
        ∑ j, ax i * ay j *
          (γ (p s ω) ^ 2 *
            ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫)) := by
    fun_prop
  have hsum_int (i : Fin n) :
      IntegrableOn
        (fun s : ℝ =>
          ∑ j, ax i * ay j *
            (γ (p s ω) ^ 2 *
              ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫))
        (Set.Ioc (0 : ℝ) t) volume :=
    (hsum_cont i).integrableOn_Ioc
  calc
    ⟪(p t ω).2 x, y⟫ =
        ∑ i, ∑ j, ax i * ay j * ⟪(p t ω).2 (b i), b j⟫ :=
      hexpand _
    _ = ∑ i, ∑ j, ax i * ay j *
        ∫ s in Set.Ioc (0 : ℝ) t,
          γ (p s ω) ^ 2 *
            ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hω i j t ht]
    _ = ∑ i, ∫ s in Set.Ioc (0 : ℝ) t,
        ∑ j, ax i * ay j *
          (γ (p s ω) ^ 2 *
            ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫) := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
    _ = ∫ s in Set.Ioc (0 : ℝ) t,
        ∑ i, ∑ j, ax i * ay j *
          (γ (p s ω) ^ 2 *
            ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) (b i), b j⟫) := by
      symm
      rw [integral_finsetSum _ (fun i _ => hsum_int i)]
    _ = ∫ s in Set.Ioc (0 : ℝ) t,
        γ (p s ω) ^ 2 *
          ⟪Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc (p s ω)) x, y⟫ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [hexpand]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
