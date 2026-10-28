-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_succ_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:47:05.101993+00:00
-- url     : https://prove2.me/submissions/00c3295e-b473-4c28-b206-7798c10dfe4d

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Positive
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Step
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_continuous_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_exists_weighted_energy_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integrable_integral_of_ae_bound_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integral_energy_le_weighted_add_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_measure_norm_gt_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_contDiff_cumulantEnergy_posterior_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_energy_integral_le_of_generator_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_cumulantEnergy_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_generator_lyapunov_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_absorption_le_envelope_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_sqrt_sum_lowerDrift_sq_le_aux_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_choose_mul_sqrt_envelope_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBoundCompact_two_of_letwinCompact_readable
import Theorems.Thm_FunctionalInequalities_KLS_compactPosterior_cumulant_bound_readable

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

section
noncomputable section
section
theorem FunctionalInequalities.KLS.BKL.envelope_nonneg {K : ℝ} (hK : 0 ≤ K) (m : ℕ) : 0 ≤ envelope K m := by
  unfold envelope
  positivity
end
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
private theorem FunctionalInequalities.KLS.BKL.Localization.energy_nonneg_aux {n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ cumulantEnergy ν d u := by
  unfold cumulantEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
private theorem FunctionalInequalities.KLS.BKL.Localization.sqrt_two_mul_aux (x y : ℝ) :
    Real.sqrt (2 * x) * Real.sqrt (2 * y) =
      2 * (Real.sqrt x * Real.sqrt y) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt 2 * Real.sqrt x * (Real.sqrt 2 * Real.sqrt y) =
        Real.sqrt 2 ^ 2 * (Real.sqrt x * Real.sqrt y) := by ring
    _ = 2 * (Real.sqrt x * Real.sqrt y) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
set_option maxHeartbeats 1000000 in
private theorem FunctionalInequalities.KLS.BKL.Localization.inductionMain_zero_le {K : ℝ} (hK : 153 ≤ K)
    {m : ℕ} (hm : 3 ≤ m) :
    FunctionalInequalities.KLS.BKL.Localization.inductionMain K m 0 ≤ envelope K m := by
  have hK0 : 0 ≤ K := by linarith
  have hb (j : ℕ) : 0 ≤ envelope K j := envelope_nonneg hK0 j
  have hsum :
      (∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) *
          Real.sqrt (envelope K (m - a + 1)) *
          (Real.sqrt (2 * envelope K (m - 1)) *
            Real.sqrt (2 * envelope K a))) =
      (2 * Real.sqrt (envelope K (m - 1))) *
        ∑ a ∈ Finset.Icc 2 (m - 2),
          ((m - 1).choose (a - 1) : ℝ) *
            Real.sqrt (envelope K a * envelope K (m - a + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [sqrt_two_mul_aux, Real.sqrt_mul (hb a)]
    ring
  have habs := absorption_le_envelope_readable (K := K) (C := 17)
    (by norm_num) (by linarith) (by linarith) hm
  rw [Real.sqrt_mul (hb (m - 1))] at habs
  unfold FunctionalInequalities.KLS.BKL.Localization.inductionMain
  simp only [add_zero]
  rw [hsum, sum_choose_mul_sqrt_envelope_readable hK0 hm]
  nlinarith only [habs]
private theorem FunctionalInequalities.KLS.BKL.Localization.inductionMain_continuous (K : ℝ) (m : ℕ) :
    Continuous (FunctionalInequalities.KLS.BKL.Localization.inductionMain K m) := by
  unfold FunctionalInequalities.KLS.BKL.Localization.inductionMain
  fun_prop
private theorem FunctionalInequalities.KLS.BKL.Localization.exists_positive_small_aux {f : ℝ → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ f δ < f 0 + ε := by
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), f x < f 0 + ε :=
    hf.continuousAt.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨η, hη, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η / 2, by positivity, he ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < η / 2)]
  linarith
set_option maxHeartbeats 1000000 in
private theorem FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral_mono_aux
    {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support}
    (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆
      Metric.closedBall 0 ρ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
    {R : ℝ} {p : ℝ → Ω → Param n}
    (hp : IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p)
    (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    weightedEnergyIntegral μ hc P (ballCutoff R) p d u S ≤
      weightedEnergyIntegral μ hc P (ballCutoff R) p d u T := by
  let E : Param n → ℝ := fun q =>
    cumulantEnergy
      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let F : Param n → ℝ := fun q => ballCutoff R q ^ 2 * E q
  have hE : Continuous E :=
    (contDiff_cumulantEnergy_posterior_readable μ hc hiso d u).continuous
  have hF : Continuous F :=
    ((lipschitzWith_ballCutoff R).continuous.pow 2).mul hE
  have hE0 (q : Param n) : 0 ≤ E q := energy_nonneg_aux _ _ _
  have hF0 (q : Param n) : 0 ≤ F q :=
    mul_nonneg (sq_nonneg _) (hE0 q)
  obtain ⟨C, _, hC⟩ := exists_cumulantEnergy_le_readable μ hc hiso hLC hρ hsupp d
  have hQ := hp.ae_Q_posSemidef_readable hiso (isCutoff_ballCutoff R)
  have hB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |F (p s w)| ≤ C * ‖u‖ ^ 2 := by
    filter_upwards [hQ] with w hw
    intro s hs
    have hg := ballCutoff_mem_Icc R (p s w)
    have hg2 : ballCutoff R (p s w) ^ 2 ≤ 1 := by
      nlinarith [hg.1, hg.2]
    rw [abs_of_nonneg (hF0 _)]
    calc
      F (p s w) ≤ 1 * E (p s w) :=
        mul_le_mul_of_nonneg_right hg2 (hE0 _)
      _ ≤ C * ‖u‖ ^ 2 := by
        simpa only [one_mul] using hC (p s w) (hw s hs).1 (hw s hs).2 u
  change (∫ w, ∫ s in Set.Ioc (0 : ℝ) S, F (p s w) ∂volume ∂P) ≤
    ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, F (p s w) ∂volume ∂P
  apply integral_mono
    (hp.integrable_integral_of_ae_bound_readable hF hB hS)
    (hp.integrable_integral_of_ae_bound_readable hF hB (hS.trans hST))
  intro w
  apply setIntegral_mono_set ((hF.comp (hp.continuous_readable w)).integrableOn_Ioc)
  · exact Filter.Eventually.of_forall fun s => hF0 (p s w)
  · filter_upwards [] with s hs
    exact ⟨hs.1, hs.2.trans hST⟩
set_option maxHeartbeats 1000000 in
/-- **The inductive step of BKL Section 6, (95)–(106), in cutoff form**: under the compact Letwin bound, Lemma 5.1
(as the hypothesis `Lemma51Bound`) and `K ≥ max {5, 9·17, 64}`, if the cutoff claim and the pointwise cumulant
bound hold at all orders `2 ≤ r < m` (`m ≥ 3`), then the cutoff claim holds at order `m`. -/
theorem solution (hL : FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound) (h51 : FunctionalInequalities.KLS.BKL.Localization.Lemma51Bound)
    {K : ℝ} (hK : 153 ≤ K) {m : ℕ} (hm : 3 ≤ m)
    (ih : ∀ r : ℕ, 2 ≤ r → r < m → FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K (r - 1))
    (ihb : ∀ r : ℕ, 2 ≤ r → r < m → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact (r - 1) (FunctionalInequalities.KLS.BKL.envelope K r)) :
    FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K (m - 1) := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hr : 2 ≤ r := by omega
  have hK0 : 0 ≤ K := by linarith
  have hb (j : ℕ) : 0 ≤ FunctionalInequalities.KLS.BKL.envelope K j := FunctionalInequalities.KLS.BKL.envelope_nonneg hK0 j
  have h8 : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact 2 8 :=
    FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact_readable hL
  change FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K r
  intro n μ hc hiso hLC u hu ε hε T hT
  obtain ⟨ρ, hρpos, hsupp⟩ :=
    hc.isBounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  have hρ : 0 ≤ ρ := hρpos.le
  obtain ⟨KL, hKL0, hKL⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.exists_generator_lyapunov_le_readable μ hc hiso hLC h8 hρ hsupp
  obtain ⟨C, hC0, hCall⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.exists_cumulantEnergy_le_readable μ hc hiso hLC hρ hsupp r
  have hC (q : FunctionalInequalities.KLS.BKL.Localization.Param n) (hS : IsSelfAdjoint q.2)
      (hQ : ∀ x, 0 ≤ ⟪q.2 x, x⟫) :
      FunctionalInequalities.KLS.BKL.cumulantEnergy
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u ≤ C := by
    simpa only [hu, one_pow, mul_one] using hCall q hS hQ u
  have hcont : Continuous (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
      FunctionalInequalities.KLS.BKL.cumulantEnergy
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) :=
    (FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulantEnergy_posterior_readable μ hc hiso r u).continuous
  obtain ⟨δ, hδ, hδlt⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.exists_positive_small_aux (FunctionalInequalities.KLS.BKL.Localization.inductionMain_continuous K (r + 1))
      (show 0 < ε / 3 by positivity)
  have hδmain : FunctionalInequalities.KLS.BKL.Localization.inductionMain K (r + 1) δ ≤ FunctionalInequalities.KLS.BKL.envelope K (r + 1) + ε / 3 := by
    have hz := FunctionalInequalities.KLS.BKL.Localization.inductionMain_zero_le hK hm
    linarith
  let T₀ : ℝ := max (max T 1) (6 * (FunctionalInequalities.KLS.BKL.envelope K r + δ) / ε)
  have hT₀one : 1 ≤ T₀ :=
    (le_max_right T 1).trans (le_max_left _ _)
  have hT₀T : T ≤ T₀ :=
    (le_max_left T 1).trans (le_max_left _ _)
  have hT₀ : 0 < T₀ := lt_of_lt_of_le zero_lt_one hT₀one
  have h2T₀ : 0 ≤ 2 * T₀ := by positivity
  have htime : 2 * (FunctionalInequalities.KLS.BKL.envelope K r + δ) / T₀ ≤ ε / 3 := by
    have hlarge : 6 * (FunctionalInequalities.KLS.BKL.envelope K r + δ) / ε ≤ T₀ := le_max_right _ _
    have hlarge' := (div_le_iff₀ hε).mp hlarge
    apply (div_le_iff₀ hT₀).mpr
    nlinarith only [hlarge']
  let Ra (a : ℕ) : ℝ :=
    if ha : 2 ≤ a ∧ a < r + 1 then
      Classical.choose
        (ih a ha.1 ha.2 n μ hc hiso hLC u hu δ hδ (2 * T₀) h2T₀)
    else 0
  let s : Finset ℕ := Finset.Icc 2 r
  have hs : s.Nonempty := ⟨r, Finset.mem_Icc.mpr ⟨hr, le_rfl⟩⟩
  let RI : ℝ := s.sup' hs Ra
  have hV0 : 0 ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov μ hc 0)
  let D : ℝ := C * (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (KL * (2 * T₀)))
  have hD : 0 ≤ D := mul_nonneg hC0 (mul_nonneg hV0 (Real.exp_pos _).le)
  let RM : ℝ := Real.sqrt (3 * D / ε) + 1
  have hRMpos : 0 < RM := by
    dsimp only [RM]
    positivity
  refine ⟨max RI RM, ?_⟩
  intro R hR Ω _ P _ W ℱ hW hℱ0 hnull p hp
  have hRI : RI ≤ R := (le_max_left _ _).trans hR
  have hRM : RM ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := hRMpos.trans_le hRM
  have hRerr : D / R ^ 2 ≤ ε / 3 := by
    have hrad : 0 ≤ 3 * D / ε := by positivity
    have hsqrtR : Real.sqrt (3 * D / ε) ≤ R := by
      have : Real.sqrt (3 * D / ε) + 1 ≤ R := hRM
      linarith
    have hsq : 3 * D / ε ≤ R ^ 2 := by
      calc
        3 * D / ε = Real.sqrt (3 * D / ε) ^ 2 := (Real.sq_sqrt hrad).symm
        _ ≤ R ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hRpos.le).mpr hsqrtR
    have hsq' := (div_le_iff₀ hε).mp hsq
    apply (div_le_iff₀ (sq_pos_of_pos hRpos)).mpr
    nlinarith only [hsq']
  have hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff (FunctionalInequalities.Probability.Diffusion.ballCutoff (V := FunctionalInequalities.KLS.BKL.Localization.Param n) R) := FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff R
  have hI (a : ℕ) (ha2 : 2 ≤ a) (har : a < r + 1) :
      FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p a u (2 * T₀) ≤
        2 * (FunctionalInequalities.KLS.BKL.envelope K a + δ) := by
    have ha : 2 ≤ a ∧ a < r + 1 := ⟨ha2, har⟩
    have hamem : a ∈ s := Finset.mem_Icc.mpr ⟨ha2, by omega⟩
    have hRa : Ra a ≤ R := (Finset.le_sup' Ra hamem).trans hRI
    have hthreshold :=
      Classical.choose_spec
        (ih a ha2 har n μ hc hiso hLC u hu δ hδ (2 * T₀) h2T₀)
    have hRa' :
        Classical.choose
          (ih a ha2 har n μ hc hiso hLC u hu δ hδ (2 * T₀) h2T₀) ≤ R := by
      simpa only [Ra, dif_pos ha] using hRa
    have hclaim := hthreshold R hRa' W ℱ hW hℱ0 hnull hp
    have hindex : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
    rw [hindex] at hclaim
    have hnonneg := FunctionalInequalities.KLS.BKL.Localization.energy_nonneg_aux (μ : Measure (EuclideanSpace ℝ (Fin n))) (a - 1) u
    linarith
  obtain ⟨t, ht, hmean⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le_readable hiso hγ hp r u hC0 hC hcont hT₀
  have ht0 : 0 ≤ t := hT₀.le.trans ht.1
  have hTt : T ≤ t := hT₀T.trans ht.1
  have hIat (a : ℕ) (ha2 : 2 ≤ a) (har : a < r + 1) :
      FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p a u t ≤
        2 * (FunctionalInequalities.KLS.BKL.envelope K a + δ) :=
    (FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral_mono_aux hiso hLC hρ hsupp hp a u ht0 ht.2).trans
      (hI a ha2 har)
  have hmean' :
      (∫ w, FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 *
        FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p t w).1 (p t w).2 :
            Measure (EuclideanSpace ℝ (Fin n))) r u ∂P) ≤ ε / 3 :=
    hmean.trans
      ((div_le_div_of_nonneg_right (hI r hr (by omega)) hT₀.le).trans htime)
  have htail := hp.measure_norm_gt_le_readable hiso hγ hℱ0 hnull hKL0 hKL ht0 hRpos
  have hexp : Real.exp (KL * t) ≤ Real.exp (KL * (2 * T₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKL0)
  have htail' :
      (P {w | R < ‖p t w‖}).toReal ≤
        FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (KL * (2 * T₀)) / R ^ 2 :=
    htail.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hV0) (sq_nonneg R))
  have htailC :
      C * (P {w | R < ‖p t w‖}).toReal ≤ ε / 3 := by
    calc
      C * (P {w | R < ‖p t w‖}).toReal ≤
          C * (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (KL * (2 * T₀)) / R ^ 2) :=
        mul_le_mul_of_nonneg_left htail' hC0
      _ = D / R ^ 2 := by
        dsimp only [D]
        ring
      _ ≤ ε / 3 := hRerr
  have hboundary :=
    FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_energy_le_weighted_add_readable hiso hp r u hC0 hC hcont ht0
  have hboundary' :
      (∫ w, FunctionalInequalities.KLS.BKL.cumulantEnergy
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p t w).1 (p t w).2 :
          Measure (EuclideanSpace ℝ (Fin n))) r u ∂P) ≤ ε / 3 + ε / 3 :=
    hboundary.trans (add_le_add hmean' htailC)
  have hgen :=
    FunctionalInequalities.KLS.BKL.Localization.energy_integral_le_of_generator_ge_readable hiso hLC hρ hsupp hγ hℱ0 hnull hp hr u
      (FunctionalInequalities.KLS.BKL.envelope K) hb (h51 n μ hc hiso hLC h8 r hr u)
      (by
        intro q hSym hQ
        have hcompact :
            IsCompact (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
              Measure (EuclideanSpace ℝ (Fin n))).support := by
          rw [FunctionalInequalities.Probability.Posterior.compactPosterior_support]
          exact hc
        have h100 : ∀ a, 2 ≤ a → a < r + 1 →
            ∀ v : EuclideanSpace ℝ (Fin n),
              FunctionalInequalities.KLS.BKL.cumulantEnergy
                (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
                  Measure (EuclideanSpace ℝ (Fin n))) (a - 1) v ≤
                FunctionalInequalities.KLS.BKL.envelope K a *
                  ⟪FunctionalInequalities.Covariance.operator
                    (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
                      Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by
          intro a ha2 har v
          exact FunctionalInequalities.KLS.compactPosterior_cumulant_bound_readable μ hc hiso hLC q.1 q.2
            hSym hQ (by omega) (ihb a ha2 har) v
        have hpoint :=
          FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux_readable (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2) hcompact
            (FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso q.1 q.2)
            (fun v hv => FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_pos μ hc hiso q.1 q.2 hv)
            r (FunctionalInequalities.KLS.BKL.envelope K) h100 u
        refine hpoint.trans (le_of_eq ?_)
        have hinterval : r - 1 = r + 1 - 2 := by omega
        rw [hinterval]
        apply Finset.sum_congr rfl
        intro a ha
        have ha' := Finset.mem_Icc.mp ha
        have hindex : r + 2 - a = r + 1 - a + 1 := by omega
        rw [hindex, Nat.add_sub_cancel])
      ht0
  have hrest :
      17 * ((r : ℝ) + 1) ^ 2 *
          FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p r u t +
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) *
            Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K (r + 1 - a + 1)) *
            (Real.sqrt (FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p r u t) *
              Real.sqrt (FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p a u t)) ≤
        FunctionalInequalities.KLS.BKL.Localization.inductionMain K (r + 1) δ := by
    unfold FunctionalInequalities.KLS.BKL.Localization.inductionMain
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hIat r hr (by omega)) (by positivity)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro a ha
      have ha' := Finset.mem_Icc.mp ha
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul
        (Real.sqrt_le_sqrt (hIat r hr (by omega)))
        (Real.sqrt_le_sqrt (hIat a ha'.1 (by omega)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have htop :=
    FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral_mono_aux hiso hLC hρ hsupp hp (r + 1) u hT hTt
  linarith only [hgen, hrest, hboundary', hδmain, htop]
