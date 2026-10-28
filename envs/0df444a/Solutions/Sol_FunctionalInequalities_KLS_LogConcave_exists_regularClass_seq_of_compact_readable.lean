-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_regularClass_seq_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:24:59.439289+00:00
-- url     : https://prove2.me/submissions/80a53d2d-8a74-4f8a-ba25-d9772cb4539d

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_Approximation
import Theorems.Thm_FunctionalInequalities_Analysis_exists_metric_diagonal_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_row_joint_tendsto_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_covarianceBilin_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_integral_bounded_tendsto_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_mean_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_norm_sq_readable
import Theorems.Thm_FunctionalInequalities_KLS_exists_regularClass_of_cond_closedBall_map_readable
import Theorems.Thm_FunctionalInequalities_KLS_exists_whitening_tendsto_moments_readable
import Theorems.Thm_FunctionalInequalities_KLS_tendsto_integral_cond_closedBall_readable

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
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- **Isotropy from moments**: finite second moment, mean zero and `∫ ⟪u, x⟫⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.isotropic_of_moments
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) (h2 : MemLp id 2 (ν : Measure E))
    (h0 : ∫ x, x ∂(ν : Measure E) = 0)
    (hcov : ∀ u v : E, ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E) = ⟪u, v⟫) :
    Isotropic ν := by
    refine ⟨h2, h0, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right (𝕜 := ℝ)
    intro v
    rw [Covariance.operator_inner]
    rw [ProbabilityTheory.covarianceBilin_apply h2]
    simpa [h0] using hcov u v
end Moments
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
open MeasureTheory Filter Topology InnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
section Euclidean
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
section
omit [CompleteSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] in
/-- A log-concave law with full affine support has support with nonempty interior. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_affineSupport_eq_top {ν : ProbabilityMeasure V₁}
    (hν : LogConcave ν) (h : affineSupport ν = ⊤) :
    (interior (ν : Measure V₁).support).Nonempty :=
  hν.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr h
end
end Euclidean
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.lintegral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : V, ENNReal.ofReal (normalizedDensity ρ s x) = 1 := by
  have hprob := smoothedLaw_probability (ν := ν) hs
  rw [isProbabilityMeasure_iff] at hprob
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs,
    withDensity_apply _ MeasurableSet.univ] at hprob
  simpa only [Measure.restrict_univ] using hprob
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedDensity ρ s) (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)).mp
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedDensity ρ s x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable]
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
/-- The normalized Gaussian convolution is exactly the tilted law of its
continuous convex logarithmic potential. Higher smoothness of the potential is a
separate analytic obligation. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_eq_tilted_potential {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    smoothedLaw ν s = (volume : Measure V).tilted (-(potential ρ s)) := by
  have hExp (x : V) : Real.exp (-potential ρ s x) =
      normalizedDensity ρ s x := by
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs x)]
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs]
  unfold Measure.tilted
  simp only [Pi.neg_apply]
  simp_rw [hExp]
  rw [integral_normalizedDensity_eq_one hρ hs]
  simp
end
end
end

section
section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Covariance of the smoothed law**: `Cov(μ * γ_s) = Cov μ + (1/(2s)) · Id` (BKL Section 2, p. 5). -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covariance_operator (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    Covariance.operator (smoothedLaw μ s) = Covariance.operator μ +
      (1 / (2 * s)) • (1 : E →L[ℝ] E) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [Covariance.operator_inner]
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    Covariance.operator_inner]
  have hone : (1 : E →L[ℝ] E) v = v := rfl
  rw [hone]
  simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using smoothedLaw_covarianceBilin_readable μ hμ2 hs v w
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.epsilon_tendsto_zero :
    Tendsto (fun s : ℝ => 1 / (2 * s)) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun s : ℝ => 2 * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp ht)
/-- The means of the smoothed laws converge (they are constant) as `s → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, y ∂μ)) := by
  apply (tendsto_const_nhds (x := ∫ y : E, y ∂μ)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_mean_readable μ hμ2 hs).symm
/-- The raw second moments of the smoothed laws converge as `s → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
  have ht : Tendsto (fun s : ℝ => (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s))
      atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero, add_zero] using
      (tendsto_const_nhds (x := ∫ y : E, ‖y‖ ^ 2 ∂μ)).add
        (epsilon_tendsto_zero.const_mul (Module.finrank ℝ E : ℝ))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_norm_sq_readable μ hμ2 hs).symm
/-- The covariance operators of the smoothed laws converge in operator norm as `s → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covariance_operator_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => Covariance.operator (smoothedLaw μ s)) atTop (𝓝 (Covariance.operator μ)) := by
  have ht : Tendsto (fun s : ℝ => Covariance.operator μ + (1 / (2 * s)) • (1 : E →L[ℝ] E))
      atTop (𝓝 (Covariance.operator μ)) := by
    simpa only [zero_smul, add_zero] using (tendsto_const_nhds (x := Covariance.operator μ)).add
      (epsilon_tendsto_zero.smul (tendsto_const_nhds (x := (1 : E →L[ℝ] E))))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_covariance_operator μ hμ2 hs).symm
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Bornology
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
section WeakConvergence
open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Weak convergence of the Gaussian smoothing**: `μ * γ_{n+1} → μ` in the topology of weak
convergence of probability laws (BKL Section 2, p. 5). -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) :
    Tendsto (fun n : ℕ => smoothedProbabilityLaw μ ((n : ℝ) + 1) (by positivity)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (smoothedLaw_integral_bounded_tendsto_readable hρ f).comp hn
end WeakConvergence
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- The quadratic tilt of the smoothed law is the law of the potential `V_s + δ/2‖·‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.quadraticTilt_smoothedLaw_eq_tilted {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (δ : ℝ) :
    (smoothedLaw μ s).tilted (fun y => -(δ / 2) * ‖y‖ ^ 2) =
      (volume : Measure E).tilted (-(fun y => potential ρ s y + δ / 2 * ‖y‖ ^ 2)) := by
  rw [smoothedLaw_eq_tilted_potential hρ hs]
  have hi : Integrable (fun y => Real.exp ((-potential ρ s) y)) (volume : Measure E) := by
    convert integrable_normalizedDensity hρ hs using 1
    funext y
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs y)]
  rw [MeasureTheory.tilted_tilted hi]
  congr 1
  funext y
  simp
  ring
/-- `2s + δ > 0`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.two_mul_add_pos {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) : 0 < 2 * s + δ := by
  linarith
/-- The law of the produced regular potential is the two-step law: Gaussian smoothing, then quadratic
tilt. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularLaw_eq_quadraticTilt {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : IsBorellDensity (μ : Measure E) volume ρ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (regularPotential_quadraticPotential hρ hs hδ).law =
      Probability.quadraticTiltLaw (smoothedProbabilityLaw μ s hs) δ hδ.le := by
  apply Subtype.ext
  change (volume : Measure E).tilted (-quadraticPotential ρ s δ) =
    (smoothedLaw (μ : Measure E) s).tilted (fun y => -(δ / 2) * ‖y‖ ^ 2)
  exact (quadraticTilt_smoothedLaw_eq_tilted hρ hs δ).symm
end
end

section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_tendsto_zero : Tendsto tiltRate atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.selected_tiltRate_tendsto_zero {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) := tiltRate_tendsto_zero.comp hk
/-- Joint convergence of the smoothings and their statistics to those of `μ`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_joint_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    Tendsto (fun n : ℕ => (gaussianSeq μ n, statistics (gaussianSeq μ n)))
      atTop (𝓝 (μ, statistics μ)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hw := smoothedProbabilityLaw_tendsto hρ
  have hm := (smoothedLaw_mean_tendsto (μ : Measure E) hμ2).comp hn
  have hsecond := (smoothedLaw_norm_sq_tendsto (μ : Measure E) hμ2).comp hn
  have hcov := (smoothedLaw_covariance_operator_tendsto (μ : Measure E) hμ2).comp hn
  exact hw.prodMk_nhds (hm.prodMk_nhds (hsecond.prodMk_nhds hcov))
/-- A diagonal `k n ≥ n` along which the two-step laws and their statistics converge to `μ`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_diagonal_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
      (∀ n, 0 < tiltRate (k n)) ∧ Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => (rowLaw μ n (k n), statistics (rowLaw μ n (k n))))
        atTop (𝓝 (μ, statistics μ)) := by
  let X := ProbabilityMeasure E × (E × (ℝ × (E →L[ℝ] E)))
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  obtain ⟨k, hkl, hk, hdiag⟩ := Analysis.exists_metric_diagonal_readable
    (fun n j => (rowLaw μ n j, statistics (rowLaw μ n j)))
    (fun n => (gaussianSeq μ n, statistics (gaussianSeq μ n)))
    (μ, statistics μ) (row_joint_tendsto_readable μ hμ2) (gaussian_joint_tendsto hρ hμ2)
  exact ⟨k, hkl, hk, fun n => tiltRate_pos (k n), selected_tiltRate_tendsto_zero hk, hdiag⟩
/-- The diagonal with the four limits (law, mean, raw second moment, covariance) exposed. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_diagonal_limits {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => rowLaw μ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  obtain ⟨k, hkl, _hk, hpos, hδ, hdiag⟩ := exists_diagonal_tendsto hρ hμ2
  exact ⟨k, hkl, hpos, hδ, hdiag.fst_nhds, hdiag.snd_nhds.fst_nhds,
    hdiag.snd_nhds.snd_nhds.fst_nhds, hdiag.snd_nhds.snd_nhds.snd_nhds⟩
/-- **Regular approximation** (BKL Section 2, p. 5): a law with a Borell density and finite second
moment is the weak limit of laws of regular potentials `V_{n+1} + δ/2‖·‖²` with curvature bounds
`δ ≤ ∇² ≤ 2(n+1) + δ`, with means, raw second moments and covariance operators converging too.
No whitened-sequence convergence is asserted. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regular_approximation_limits
    {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential ρ ((n : ℝ) + 1) (tiltRate (k n))) (tiltRate (k n))
        (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => rowLaw μ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  obtain ⟨k, hkl, hpos, hδ, hw, hm, hsecond, hcov⟩ := exists_diagonal_limits hρ hμ2
  exact ⟨k, hkl, hpos, hδ, fun n => regularPotential_quadraticPotential hρ (by positivity) (hpos n),
    fun n => two_mul_add_pos (by positivity) (hpos n), hw, hm, hsecond, hcov⟩
/-- It equals the two-step law. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularSeq_eq_rowLaw {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (n k : ℕ) :
    regularSeq hρ n k = rowLaw μ n k :=
  regularLaw_eq_quadraticTilt hρ (by positivity) (tiltRate_pos k)
/-- The regular approximation stated for `regularSeq`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits
    {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential ρ ((n : ℝ) + 1) (tiltRate (k n))) (tiltRate (k n))
        (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => regularSeq hρ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  simpa only [regularSeq_eq_rowLaw] using
    exists_regular_approximation_limits hρ hμ2
end
end
end

section
open MeasureTheory Filter Topology
noncomputable section
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An isotropic law has full affine support (owner: `KLS/IsotropicSupport.lean`). -/
theorem FunctionalInequalities.KLS.LogConcave.affineSupport_eq_top_of_isotropic {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ :=
  hiso.affineSupport_eq_top
/-- An isotropic log-concave law has a Borell density with respect to Lebesgue measure. -/
theorem FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_isotropic {μ : ProbabilityMeasure E}
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    ∃ ρ : E → ℝ, KLS.IsBorellDensity (μ : Measure E) volume ρ := by
  have hi := hLC.interior_support_nonempty_of_affineSupport_eq_top (affineSupport_eq_top_of_isotropic hiso)
  exact hLC.exists_isBorellDensity_of_interior_support_nonempty volume hi
    (hLC.absolutelyContinuous_of_interior_support_nonempty volume hi)
end
end
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Metric
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
/-- **Compact regular approximation.** A compactly supported isotropic log-concave law is the limit, in all mixed
linear moments of degree `≤ 4`, of isotropic laws `1_K e^{-W} dx` with `K` compact convex with nonempty interior and `W`
smooth and uniformly convex. Every term is isotropic: the whitened Gaussian-smoothed ball conditionings are taken beyond
the index where whitening is exact. Log-concavity of each term follows from its density (`logConcave_of_eq_regularClass`). -/
theorem solution {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ)
    (hcompact : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) :
    ∃ ζ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      (∀ j, FunctionalInequalities.KLS.Isotropic (ζ j) ∧ ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
        (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ ContDiff ℝ ∞ W ∧
          ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
          (ζ j : Measure (EuclideanSpace ℝ (Fin n))) =
            (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
              (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) ∧
      ∀ d ≤ 4, ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
        Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ζ j : Measure (EuclideanSpace ℝ (Fin n)))) atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨r, hr⟩ :=
    Bornology.IsBounded.subset_closedBall hcompact.isBounded (0 : E)
  let r₀ : ℝ := max r 0
  let R : ℝ := r₀ + 1
  have hr₀ : (μ : Measure E) (closedBall (0 : E) r₀)ᶜ = 0 := by
    have hsub : (μ : Measure E).support ⊆ closedBall (0 : E) r₀ :=
      hr.trans (closedBall_subset_closedBall (le_max_left r 0))
    exact measure_mono_null (compl_subset_compl.mpr hsub)
      Measure.measure_compl_support
  have hR : 0 < R := by
    have : 0 ≤ r₀ := le_max_right r 0
    dsimp [R]
    linarith
  have hrR : r₀ < R := by
    dsimp [R]
    linarith
  have hμR : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0 :=
    measure_mono_null
      (compl_subset_compl.mpr (closedBall_subset_closedBall hrR.le)) hr₀
  obtain ⟨ρ, hρ⟩ :=
    FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_isotropic hLC hiso
  obtain ⟨k, _hk, _hkpos, _hkδ, hkV, _hkupper, hweak, _hmean, _hsecond, _hcov⟩ :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits hρ hiso.memLp_two
  let ν : ℕ → ProbabilityMeasure E :=
    fun j => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularSeq hρ j (k j)
  have hνV (j : ℕ) :
      FunctionalInequalities.KLS.RegularPotential
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.quadraticPotential ρ
          ((j : ℝ) + 1)
          (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate (k j)))
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate (k j))
        (2 * ((j : ℝ) + 1) +
          FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate (k j)) :=
    hkV j
  have hνeq (j : ℕ) : ν j = (hνV j).law := rfl
  have hweak' : Tendsto ν atTop (𝓝 μ) := hweak
  have hνball (j : ℕ) :
      0 < (ν j : Measure E) (closedBall (0 : E) R) := by
    rw [hνeq j]
    have hv :
        0 < (volume : Measure E) (closedBall (0 : E) R) :=
      Measure.measure_pos_of_mem_nhds volume
        (closedBall_mem_nhds (0 : E) hR)
    have hac :
        (volume : Measure E) ≪ ((hνV j).law : Measure E) :=
      MeasureTheory.absolutelyContinuous_tilted (hνV j).integrable_exp_neg
    by_contra hz
    have hz' : ((hνV j).law : Measure E) (closedBall (0 : E) R) = 0 :=
      nonpos_iff_eq_zero.mp (le_of_not_gt hz)
    exact (ne_of_gt hv) (hac hz')
  let lam : ℕ → ProbabilityMeasure E := fun j =>
    ⟨ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R),
      ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt (hνball j))⟩
  have hlam (j : ℕ) :
      (lam j : Measure E) =
        ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R) :=
    rfl
  have hlam_supp (j : ℕ) :
      (lam j : Measure E) (closedBall (0 : E) R)ᶜ = 0 := by
    rw [hlam j, ProbabilityTheory.cond_apply measurableSet_closedBall]
    simp
  have hlam_mom :
      ∀ d ≤ 4, ∀ v : Fin d → E,
        Tendsto
          (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam j : Measure E))
          atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d _hd v
    exact FunctionalInequalities.KLS.tendsto_integral_cond_closedBall_readable
      hweak' hrR hr₀ (by fun_prop)
  obtain ⟨L, c, hwhite, hwhmom⟩ :=
    FunctionalInequalities.KLS.exists_whitening_tendsto_moments_readable
      hiso hlam_supp hμR hlam_mom
  let η : ℕ → ProbabilityMeasure E := fun j =>
    MeasureTheory.ProbabilityMeasure.map (lam j)
      (by fun_prop :
        AEMeasurable (fun x : E => L j (x - c j)) (lam j : Measure E))
  have hηsupp (j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧
        (η j : Measure E) (closedBall (0 : E) C)ᶜ = 0 := by
    let f : E → E := fun x => L j (x - c j)
    have hf : Continuous f := by fun_prop
    obtain ⟨C₀, hC₀⟩ :=
      (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
    let C : ℝ := max C₀ 0
    refine ⟨C, le_max_right _ _, ?_⟩
    change (Measure.map f (lam j : Measure E)) (closedBall (0 : E) C)ᶜ = 0
    rw [Measure.map_apply hf.measurable measurableSet_closedBall.compl]
    refine measure_mono_null (t := (closedBall (0 : E) R)ᶜ) ?_ (hlam_supp j)
    intro x hx hxR
    apply hx
    rw [mem_closedBall, dist_zero_right]
    exact (hC₀ x hxR).trans (le_max_left _ _)
  have hηmem2 (j : ℕ) : MemLp id 2 (η j : Measure E) := by
    obtain ⟨C, _hC, hs⟩ := hηsupp j
    refine MemLp.of_bound continuous_id.aestronglyMeasurable C ?_
    filter_upwards [ae_iff.mpr hs] with x hx
    simpa only [id_eq, dist_zero_right] using mem_closedBall.mp hx
  have hηintegral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (j : ℕ) {f : E → F} (hf : Continuous f) :
      ∫ y, f y ∂(η j : Measure E) =
        ∫ x, f (L j (x - c j)) ∂(lam j : Measure E) := by
    let g : E → E := fun x => L j (x - c j)
    have hg : Continuous g := by fun_prop
    change (∫ y, f y ∂Measure.map g (lam j : Measure E)) =
      ∫ x, f (g x) ∂(lam j : Measure E)
    exact MeasureTheory.integral_map hg.aemeasurable hf.aestronglyMeasurable
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hwhite
  have hηiso (j : ℕ) (hj : j₀ ≤ j) : FunctionalInequalities.KLS.Isotropic (η j) := by
    have hwj := hj₀ j hj
    apply FunctionalInequalities.KLS.isotropic_of_moments (η j) (hηmem2 j)
    · exact (hηintegral j (f := fun x : E => x) continuous_id).trans hwj.1
    · intro u v
      exact (hηintegral j
        (f := fun x : E => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)).trans (hwj.2 u v)
  have hηmom :
      ∀ d ≤ 4, ∀ v : Fin d → E,
        Tendsto
          (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(η j : Measure E))
          atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d hd v
    apply (hwhmom d hd v).congr'
    filter_upwards [] with j
    exact (hηintegral j
      (f := fun x : E => ∏ i, ⟪v i, x⟫) (by fun_prop)).symm
  refine ⟨fun j => η (j + j₀), fun j => ⟨hηiso (j + j₀) (by omega), ?_⟩, ?_⟩
  · obtain ⟨K, W, κ, hκ, hK, hKconv, hKint, hW, hWconv, hmap⟩ :=
      FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map_readable
        (hνV (j + j₀)) hR (L (j + j₀)) (c (j + j₀))
    refine ⟨K, W, κ, hκ, hK, hKconv, hKint, hW, hWconv, ?_⟩
    change
      Measure.map (fun x : E => L (j + j₀) (x - c (j + j₀)))
          (ProbabilityTheory.cond (ν (j + j₀) : Measure E) (closedBall (0 : E) R)) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))
    rw [hνeq (j + j₀)]
    exact hmap
  · intro d hd v
    exact (hηmom d hd v).comp (tendsto_add_atTop_nat j₀)
