-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_lyapunov_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:37:46.638454+00:00
-- url     : https://prove2.me/submissions/5c429f63-2c25-49a8-a1d9-abba41a2cfc3

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
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment
import Theorems.Thm_FunctionalInequalities_Analysis_le_mul_exp_of_le_add_integral_readable
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_continuous_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_dynkin_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integrable_integral_of_ae_bound_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_contDiff_lyapunov_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_locallyLipschitz_noise_readable
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_locallyLipschitz_inverseSqrt_covariance_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorCovariance_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorMean_joint_readable

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
/-- **Joint smoothness of the drift** `A⁻¹ a` of (67). -/
theorem FunctionalInequalities.KLS.Isotropic.contDiff_covarianceDrift_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
        (posteriorMean μ p.1 p.2)) :=
  (Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).clm_apply
    (contDiff_posteriorMean_joint_readable μ hc)
/-- **Coefficient regularity of (67)** (BKL p. 19): the coefficient map `(c, Q) ↦ (A^{-1/2}, A⁻¹ a, A⁻¹)` of the
localization equations, built from `compactPosterior`, is locally Lipschitz on all of `E × (E →L[ℝ] E)` for a
compactly supported isotropic prior (all finite `(c, Q)`, including `Q = 0`, non-symmetric `Q` and dimension
zero). Deterministic: no process, strong solution or non-explosion statement. -/
theorem FunctionalInequalities.KLS.Isotropic.locallyLipschitz_coefficients67 (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    LocallyLipschitz (fun p : E × (E →L[ℝ] E) =>
      (inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)),
       (Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
         (posteriorMean μ p.1 p.2),
        Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))))) :=
  (Isotropic.locallyLipschitz_inverseSqrt_covariance_joint_readable μ hc hiso).prodMk
    (((Isotropic.contDiff_covarianceDrift_joint μ hc hiso).of_le (by simp)).locallyLipschitz.prodMk
      ((Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).of_le (by simp)).locallyLipschitz)
end JointCoefficients
end
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
/-- `𝓛_γ F = γ² 𝓛 F`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_cutoff (γ : Param n → ℝ) (F : Param n → ℝ) (p : Param n) :
    diffusionGenerator (cutoffDrift μ hc γ) (cutoffNoise μ hc γ) F p =
      γ p ^ 2 * generator μ hc F p := by
  simp only [diffusionGenerator, generator, cutoffDrift, cutoffNoise, map_smul,
    smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring
/-- The drift of (67) is locally Lipschitz. -/
theorem FunctionalInequalities.KLS.BKL.Localization.locallyLipschitz_drift (hiso : KLS.Isotropic μ) : LocallyLipschitz (drift μ hc) := by
  have h := (LipschitzWith.prod_snd.locallyLipschitz).comp
    (Isotropic.locallyLipschitz_coefficients67 μ hc hiso)
  show LocallyLipschitz (fun p : Param n => drift μ hc p)
  simpa only [Function.comp_def, drift, cov] using h
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
end VectorVersion
end
end

section
noncomputable section
open scoped RealInnerProductSpace
section
variable {n : ℕ}
theorem FunctionalInequalities.Analysis.hsNormSq_nonneg (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : 0 ≤ hsNormSq M := by
  unfold hsNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
end
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
theorem FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov (p : Param n) : 1 ≤ lyapunov μ hc p := by
  unfold lyapunov
  have h₁ := sq_nonneg ‖p.1‖
  have h₂ := hsNormSq_nonneg p.2
  have h₃ := sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))
  linarith
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
private theorem FunctionalInequalities.KLS.BKL.Localization.continuous_generator_of_contDiff
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : KLS.Isotropic μ) {F : Param n → ℝ} (hF : ContDiff ℝ 3 F) :
    Continuous (generator μ hc F) := by
  have hdrift : Continuous (drift μ hc) :=
    (locallyLipschitz_drift μ hc hiso).continuous
  have hfirst : Continuous (fun q => fderiv ℝ F q (drift μ hc q)) := by
    have h :=
      hF.continuous_fderiv_apply (by norm_num :
        (3 : WithTop ℕ∞) ≠ 0)
    exact h.comp (continuous_id.prodMk hdrift)
  have hsecond (k : Fin n) :
      Continuous
        (fun q => fderiv ℝ (fderiv ℝ F) q
          (noise μ hc q k) (noise μ hc q k)) := by
    have hnoise : Continuous (fun q => noise μ hc q k) :=
      (locallyLipschitz_noise_readable μ hc hiso k).continuous
    have h :=
      (hF.fderiv_right
        (m := (1 : WithTop ℕ∞))
        (by norm_num :
          (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))).continuous_fderiv_apply
        (by norm_num :
          (1 : WithTop ℕ∞) ≠ 0)
    have h' : Continuous
        (fun q => fderiv ℝ (fderiv ℝ F) q (noise μ hc q k)) :=
      h.comp (continuous_id.prodMk hnoise)
    exact h'.clm_apply hnoise
  have hsum :
      Continuous
        (fun q => ∑ k, fderiv ℝ (fderiv ℝ F) q
          (noise μ hc q k) (noise μ hc q k)) := by
    exact continuous_finsetSum Finset.univ (by
      intro k hk
      exact hsecond k)
  unfold generator diffusionGenerator
  exact hfirst.add (continuous_const.mul hsum)
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc) q ≤ K * FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc q)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω)) P ∧
      ∫ ω, FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω) ∂P ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (K * t) := by
  classical
  let F : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc
  let g : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q => γ q ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc F q
  let φ : ℝ → ℝ := fun s => ∫ ω, F (p s ω) ∂P
  have hF : ContDiff ℝ 2 F :=
    (FunctionalInequalities.KLS.BKL.Localization.contDiff_lyapunov_readable μ hc hiso).of_le (WithTop.coe_le_coe.mpr le_top)
  have hF3 : ContDiff ℝ 3 F :=
    (FunctionalInequalities.KLS.BKL.Localization.contDiff_lyapunov_readable μ hc hiso).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγc : Continuous γ :=
    hγ.lipschitz.choose_spec.continuous
  have hgen : Continuous (FunctionalInequalities.KLS.BKL.Localization.generator μ hc F) :=
    FunctionalInequalities.KLS.BKL.Localization.continuous_generator_of_contDiff μ hc hiso hF3
  have hgc : Continuous g :=
    (hγc.pow 2).mul hgen
  have hgcs : HasCompactSupport g := by
    refine hγ.compactSupport.mono ?_
    intro q hq
    by_contra hqγ
    have hγq : γ q = 0 := by
      exact not_ne_iff.mp hqγ
    exact hq (by simp [g, hγq])
  obtain ⟨B₀, hB₀⟩ := hgc.bounded_above_of_compact_support hgcs
  let B : ℝ := max B₀ 0
  have hB : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, ‖g q‖ ≤ B := by
    intro q
    exact (hB₀ q).trans (le_max_left _ _)
  have hB0 : 0 ≤ B :=
    le_max_right _ _
  have hgb : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |g (p s ω)| ≤ B := by
    filter_upwards [] with ω s hs
    simpa only [Real.norm_eq_abs] using hB (p s ω)
  have hdyn (s : ℝ) (hs : 0 ≤ s) :
      Integrable (fun ω => F (p s ω)) P ∧
        φ s - F 0 =
          ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P := by
    simpa only [F, g, φ, FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_cutoff] using
      h.dynkin_readable hiso hγ hℱ0 hnull hF hs
  have hinner_bound (s : ℝ) (hs : 0 ≤ s) (ω : Ω) :
      ‖∫ r in Set.Ioc (0 : ℝ) s, g (p r ω)‖ ≤ B * s := by
    calc
      ‖∫ r in Set.Ioc (0 : ℝ) s, g (p r ω)‖ ≤
          ∫ r in Set.Ioc (0 : ℝ) s, ‖g (p r ω)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r in Set.Ioc (0 : ℝ) s, B := by
        apply setIntegral_mono_on
        · exact (hgc.comp (h.continuous_readable ω)).norm.integrableOn_Ioc
        · exact continuous_const.integrableOn_Ioc
        · exact measurableSet_Ioc
        · intro r hr
          exact hB (p r ω)
      _ = B * s := by
        simp [hs]
        ring
  have hphi_bound (s : ℝ) (hs : 0 ≤ s) :
      |φ s| ≤ F 0 + B * s := by
    have hout₀ :=
      norm_integral_le_of_norm_le_const
        (μ := P)
        (f := fun ω => ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω))
        (C := B * s)
        (Filter.Eventually.of_forall (hinner_bound s hs))
    have hout :
        ‖∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P‖ ≤ B * s := by
      simpa [Measure.real_def, IsProbabilityMeasure.measure_univ] using hout₀
    have heq :
        φ s = F 0 + ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P := by
      linarith [(hdyn s hs).2]
    rw [heq]
    calc
      |F 0 + ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P| ≤
          |F 0| + ‖∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P‖ :=
        abs_add_le _ _
      _ ≤ F 0 + B * s := by
        have hF0 : 0 ≤ F 0 := by
          exact le_trans (by norm_num) (FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov μ hc 0)
        rw [abs_of_nonneg hF0]
        linarith
  have hphib : ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) t, |φ s| ≤ C := by
    refine ⟨F 0 + B * t, ?_⟩
    intro s hs
    have hst : B * s ≤ B * t :=
      mul_le_mul_of_nonneg_left hs.2 hB0
    linarith [hphi_bound s hs.1]
  let Φ : FunctionalInequalities.KLS.BKL.Localization.Param n ≃L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) :=
    FunctionalInequalities.Probability.Diffusion.stateEquiv (FunctionalInequalities.KLS.BKL.Localization.Param n)
  have h' := h
  change FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW
    (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ))
    (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h'
  obtain ⟨_, _, _, hv⟩ := h'
  have h1 : Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun ω s => Φ (p s ω)))
    exact hv.measurable_uncurry
  have hpmeas : Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
    have h2 := Φ.symm.continuous.measurable.comp h1
    change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at h2
    simpa only [Φ.symm_apply_apply] using h2
  have hmF : Measurable (fun z : Ω × ℝ => F (p z.2 z.1)) :=
    hF.continuous.measurable.comp hpmeas
  have hphim : Measurable φ := by
    have hs := hmF.stronglyMeasurable.integral_prod_left' (μ := P)
    simpa only [φ] using hs.measurable
  have hprodF (u : ℝ) (hu : 0 ≤ u) :
      Integrable
        (fun z : Ω × ℝ => F (p z.2 z.1))
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) u))) := by
    let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) u)
    change Integrable (fun z : Ω × ℝ => F (p z.2 z.1)) (P.prod ν)
    rw [integrable_prod_iff'
      (h1f := hmF.stronglyMeasurable.aestronglyMeasurable)]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (hdyn s hs.1.le).1
    · have hnormm :
          Measurable (fun z : Ω × ℝ => ‖F (p z.2 z.1)‖) :=
        hmF.norm
      have hnormsm :
          AEStronglyMeasurable
            (fun s => ∫ ω, ‖F (p s ω)‖ ∂P) ν :=
        hnormm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
      apply Integrable.of_bound hnormsm (F 0 + B * u)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs0 : 0 ≤ s := hs.1.le
      have hnormeq :
          (∫ ω, ‖F (p s ω)‖ ∂P) = φ s := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg]
        change 0 ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p s ω)
        exact le_trans (by norm_num) (FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov μ hc _)
      have hφnonneg : 0 ≤ φ s := by
        rw [← hnormeq]
        exact integral_nonneg (fun ω => norm_nonneg _)
      rw [hnormeq, Real.norm_eq_abs, abs_of_nonneg hφnonneg]
      have hsu : B * s ≤ B * u :=
        mul_le_mul_of_nonneg_left hs.2 hB0
      linarith [hphi_bound s hs0, le_abs_self (φ s)]
  have hswapF (u : ℝ) (hu : 0 ≤ u) :
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P =
        ∫ s in Set.Ioc (0 : ℝ) u, φ s := by
    simpa only [φ] using
      integral_integral_swap (hprodF u hu)
  have hmono (u : ℝ) (hu : 0 ≤ u) :
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ∂volume ∂P ≤
        K * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P := by
    have hQ := h.ae_Q_posSemidef_readable hiso hγ
    have hle :
        ∀ᵐ ω ∂P, ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ≤
          K * ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) := by
      filter_upwards [hQ] with ω hω
      have hset :
          ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ≤
            ∫ s in Set.Ioc (0 : ℝ) u, K * F (p s ω) := by
        apply setIntegral_mono_on
        · exact (hgc.comp (h.continuous_readable ω)).integrableOn_Ioc
        · exact
            (continuous_const.mul
              (hF.continuous.comp (h.continuous_readable ω))).integrableOn_Ioc
        · exact measurableSet_Ioc
        · intro s hs
          have hq := hω s hs.1.le
          have hgen' :
              FunctionalInequalities.KLS.BKL.Localization.generator μ hc F (p s ω) ≤ K * F (p s ω) := by
            simpa only [F] using hK (p s ω) hq.1 hq.2
          have hγ0 : 0 ≤ γ (p s ω) :=
            (hγ.mem_Icc (p s ω)).1
          have hγ1 : γ (p s ω) ≤ 1 :=
            (hγ.mem_Icc (p s ω)).2
          have hγsq : γ (p s ω) ^ 2 ≤ 1 := by
            nlinarith [mul_nonneg hγ0 (sub_nonneg.mpr hγ1)]
          by_cases hg : 0 ≤ FunctionalInequalities.KLS.BKL.Localization.generator μ hc F (p s ω)
          · dsimp [g]
            calc
              γ (p s ω) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc F (p s ω) ≤
                  FunctionalInequalities.KLS.BKL.Localization.generator μ hc F (p s ω) := by
                nlinarith [mul_le_mul_of_nonneg_right hγsq hg]
              _ ≤ K * F (p s ω) := hgen'
          · have hleft :
                g (p s ω) ≤ 0 := by
              dsimp [g]
              exact
                mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
                  (le_of_not_ge hg)
            have hright : 0 ≤ K * F (p s ω) := by
              exact
                mul_nonneg hK0
                  (le_trans (by norm_num) (FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov μ hc _))
            exact hleft.trans hright
      rw [integral_const_mul] at hset
      exact hset
    have hgi :=
      h.integrable_integral_of_ae_bound_readable hgc hgb hu
    have hFi :
        Integrable
          (fun ω => ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω))
          P := by
      simpa using (hprodF u hu).integral_prod_left
    have hKFi :
        Integrable
          (fun ω => K * ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω))
          P :=
      hFi.const_mul K
    calc
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, g (p s ω) ∂volume ∂P ≤
          ∫ ω, K * ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P :=
        integral_mono_ae hgi hKFi hle
      _ = K * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) u, F (p s ω) ∂volume ∂P := by
        rw [integral_const_mul]
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) t,
      φ s ≤ F 0 + K * ∫ r in Set.Ioc (0 : ℝ) s, φ r := by
    intro s hs
    have hd := hdyn s hs.1
    have hm := hmono s hs.1
    have hswap := hswapF s hs.1
    calc
      φ s =
          F 0 + ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, g (p r ω) ∂volume ∂P := by
        linarith [hd.2]
      _ ≤ F 0 + K * ∫ ω, ∫ r in Set.Ioc (0 : ℝ) s, F (p r ω) ∂volume ∂P := by
        linarith [hm]
      _ = F 0 + K * ∫ r in Set.Ioc (0 : ℝ) s, φ r := by
        rw [hswap]
  have hgr := FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral_readable hK0 hphim hphib hineq
  have hbound := hgr t ⟨ht, le_rfl⟩
  have hIt := (hdyn t ht).1
  constructor
  · simpa only [F] using hIt
  · simpa only [φ, F] using hbound
