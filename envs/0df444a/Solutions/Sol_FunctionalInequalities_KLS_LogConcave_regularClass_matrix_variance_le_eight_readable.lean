-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.regularClass_matrix_variance_le_eight_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:32:18.973821+00:00
-- url     : https://prove2.me/submissions/27e8af6b-4932-4b0d-a1d4-1dcaa6ba034c

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_RegularClass
import Theorems.Thm_FunctionalInequalities_Analysis_exists_symmetric_isUnit_matrix_sequence_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_spectral_geometry_readable
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_trace_integral_extension_mul_of_ae_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_mean_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_smoothed_quadratic_variance_le_latent_energy_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_trace_quadratic_le_two_mul_trace_sq_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_logConcave_of_eq_regularClass_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_source_stein_identity_of_bounded_lipschitz_test_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_sum_integral_spectral_noise_energy_le_readable
import Theorems.Thm_FunctionalInequalities_Probability_quadratic_variance_le_centered_noise_convolution_readable
import Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_quadratic_matrix_forms_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_trace_energy_readable

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
open scoped ENNReal
section
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_four {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : ℝ} (hs : 0 < s) : MemLp id 4 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun x : E => Real.exp ((1 : ℝ) * ‖x‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  have hp := Probability.integrable_norm_pow_of_integrable_exp_norm
    (by norm_num : (0 : ℝ) < 1) he 4
  apply (integrable_norm_rpow_iff (f := (id : E → E)) continuous_id.aestronglyMeasurable
    (by norm_num : (4 : ENNReal) ≠ 0) (by simp : (4 : ENNReal) ≠ ∞)).mp
  simpa using hp
end
end
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.map_linear_memLp_four (μ : Measure E) (S : E →L[ℝ] E)
    (hμ4 : MemLp id 4 μ) : MemLp id 4 (μ.map S) := by
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable S.continuous.measurable.aemeasurable).2
  exact S.comp_memLp' hμ4
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end HessianEntryBounds
end

section
noncomputable section
open Matrix MeasureTheory
section AEPosSemidefTraceIntegral
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The symmetric trace-integral extension of `symmetric_trace_integral_extension` from almost-everywhere positive
semidefinite matrix fields: the bound `∫ tr(A H A H) ≤ 2 tr(A A)` for every PSD `A` gives it for every symmetric `B`.
Arbitrary finite index type (empty allowed) and measure. -/
theorem FunctionalInequalities.Analysis.symmetric_trace_integral_extension_of_ae_posSemidef
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤
          2 * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        2 * (B * B).trace :=
  symmetric_trace_integral_extension_mul_of_ae_posSemidef_readable ν H hH_meas hH_psd hPSD hB
end
end AEPosSemidefTraceIntegral
end
end

section
open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff Matrix.Norms.Frobenius
noncomputable section
section
/-- `⟪v, T w⟫ = ⟪T v, w⟫` for symmetric `T`. -/
theorem FunctionalInequalities.Probability.Stein.inner_action_swap {n : ℕ} (T : KernelMatrix n) (hT : ∀ i j, T i j = T j i)
    (v w : EuclideanSpace ℝ (Fin n)) : ⟪v, action T w⟫ = ⟪action T v, w⟫ := by
  simp only [action, PiLp.inner_apply, Real.inner_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT i j]
  ring
end
end
noncomputable section
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.Probability.Stein.action_mul {n : ℕ} (A B : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (A*B) x = action A (action B x) := by
  apply WithLp.ofLp_injective
  exact (Matrix.mulVec_mulVec x.ofLp A B).symm
theorem FunctionalInequalities.Probability.Stein.action_add {n : ℕ} (A B : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (A+B) x = action A x + action B x := by
  apply WithLp.ofLp_injective
  exact Matrix.add_mulVec A B x.ofLp
theorem FunctionalInequalities.Probability.Stein.action_smul {n : ℕ} (t : ℝ) (A : KernelMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    action (t • A) x = t • action A x := by
  apply WithLp.ofLp_injective
  exact Matrix.smul_mulVec t A x.ofLp
theorem FunctionalInequalities.Probability.Stein.action_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    action (1 : KernelMatrix n) x = x := by
  apply WithLp.ofLp_injective
  exact Matrix.one_mulVec x.ofLp
end
end
end

section
section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
section RegularMomentWeakTheorem25
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1000000 in
private theorem FunctionalInequalities.Analysis.actual_source_weak_theorem25_data :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ((      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let D := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        (B * (Matrix.of fun a b => T x i a b) * B * (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
        (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace := by
  obtain ⟨u, L, LF, T, hOld, hEnergy⟩ := exists_regular_moment_weak_trace_energy_readable
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hOld.1.1
  rcases hcopy with ⟨hbase, _hcutoffs⟩
  rcases hbase with ⟨hc, hl, hnrm, _hm, hC1, hG, _hF, _hw, hdata, hT, _he,
    _hfirst, hInv, hmean, _hq, _hflux, _hweighted, _hbounded⟩
  refine ⟨u, L, LF, T, ⟨hOld, hEnergy⟩, ?_⟩
  intro B hB
  have hexp : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnrm]; norm_num)
  let nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u), isProbabilityMeasure_tilted hexp⟩
  obtain ⟨hD, hhalf⟩ := hEnergy B hB
  exact KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq_readable
    (nu := nu) rfl hc hC1 hG hl hnrm (hdata.mono fun _ hx => hx.1) T hT
    (fun i j K hK => (hInv i i j).2.2 K hK) hmean B hB hD hhalf
end
end RegularMomentWeakTheorem25
section RegularMomentWeakSymmetricTraceBound
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1000000 in
private theorem FunctionalInequalities.Analysis.actual_source_weak_symmetric_trace_bound_data :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ((      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let D := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        (B * (Matrix.of fun a b => T x i a b) * B * (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
        (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace := by
  obtain ⟨u, L, LF, T, hOld, hPSD⟩ := actual_source_weak_theorem25_data
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hOld.1.1.1
  rcases hcopy with ⟨hbase, _hcutoffs⟩
  rcases hbase with ⟨_hc, _hl, _hnrm, _hm, _hC1, _hG, _hF, _hw, hdata, _hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  have hAE : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)),
      (hessianMatrix u x).PosSemidef :=
    (tilted_absolutelyContinuous (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)).ae_le
      (hdata.mono fun _ hx => hx.1.posSemidef)
  refine ⟨u, L, LF, T, hOld, ?_⟩
  intro B hB
  exact symmetric_trace_integral_extension_of_ae_posSemidef
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))
    (fun x => hessianMatrix u x) (fun i j => measurable_hessianMatrix_entry u i j)
    hAE hPSD hB
end
end RegularMomentWeakSymmetricTraceBound
section RegularMomentWeightedWeakPairing
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1000000 in
private theorem FunctionalInequalities.Analysis.actual_source_weighted_weak_pairing_data :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
(      ((      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let D := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        (B * (Matrix.of fun a b => T x i a b) * B * (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
        (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace) ∧
      ∀ (eta : EuclideanSpace ℝ (Fin n) → ℝ) (Leta : NNReal) (C : ℝ),
        LipschitzWith Leta eta → (∀ x, ‖eta x‖ ≤ C) →
        ∀ v : EuclideanSpace ℝ (Fin n),
        Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        Integrable (fun x => eta x * fderiv ℝ u x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ x, eta x * fderiv ℝ u x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  obtain ⟨u, L, LF, T, hPayload⟩ := actual_source_weak_symmetric_trace_bound_data
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hPayload.1.1.1.1
  rcases hcopy with ⟨hbase, _hcutoffs⟩
  rcases hbase with ⟨_hc, hl, hnrm, _hm, _hC1, _hG, _hF, _hw, _hdata, _hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  refine ⟨u, L, LF, T, hPayload, ?_⟩
  intro eta Leta C heta hbound v
  exact integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_readable
    hl heta C hbound hnrm v
end
end RegularMomentWeightedWeakPairing
section RegularMomentWeakSteinCoupling
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1000000 in
/-- Weak source Stein coupling at one regular moment witness: at the same `u`, `L`, `LF`, `T` the whole payload (cutoff testing,
trace contraction, conservativity, half energy, all-symmetric Theorem 2.5 trace bound and bounded-Lipschitz weighted
pairing) is retained, and every C1 globally Lipschitz globally bounded test satisfies the coordinate source Stein identity. -/
theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_stein_coupling :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
((      ((      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let D := fun x => ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        (B * (Matrix.of fun a b => T x i a b) * B * (Matrix.of fun a b => T x j a b)).trace
      Integrable D ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, D x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤
        (1 / 2 : ℝ) * ∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace) ∧
      ∀ (eta : EuclideanSpace ℝ (Fin n) → ℝ) (Leta : NNReal) (C : ℝ),
        LipschitzWith Leta eta → (∀ x, ‖eta x‖ ≤ C) →
        ∀ v : EuclideanSpace ℝ (Fin n),
        Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        Integrable (fun x => eta x * fderiv ℝ u x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ x, eta x * fderiv ℝ u x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (Lf : NNReal) (C : ℝ),
        ContDiff ℝ 1 f → LipschitzWith Lf f → (∀ x, ‖f x‖ ≤ C) → ∀ i : Fin n,
        Integrable (fun y => gradient u y i * f (gradient u y))
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        Integrable (fun y => ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ y, gradient u y i * f (gradient u y)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          ∫ y, (∑ j, hessianMatrix u y i j * gradient f (gradient u y) j)
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  obtain ⟨u, L, LF, T, hPayload⟩ := actual_source_weighted_weak_pairing_data
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hPayload.1.1.1.1.1
  rcases hcopy with ⟨hbase, _hcutoffs⟩
  rcases hbase with ⟨_hc, hl, hnrm, _hm, hC1, hG, _hF, _hw, _hdata, _hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  refine ⟨u, L, LF, T, hPayload, ?_⟩
  intro f Lf C hf hfLip hbound i
  exact KLS.LogConcave.source_stein_identity_of_bounded_lipschitz_test_readable hC1 hl hG hnrm
    hf hfLip C hbound i
end
end RegularMomentWeakSteinCoupling
section RegularMomentHessianTraceBound
open MeasureTheory Set Matrix
open FunctionalInequalities.Analysis.BakryEmery
section
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1000000 in
/-- The properties of one actual regular moment witness used by the Letwin regular-class assembly, as a flat conjunction at
the same `u` and `L` produced by `exists_regular_moment_weak_stein_coupling`: convexity, Lipschitz bound, normalization,
pushforward to `μ`, `C¹` with `16/κ`-Lipschitz gradient, the a.e. positive definite Hessian with log-det identity and
`16/κ` cap, integrable Hessian entries with mean `Id`, and the weak Theorem 2.5 bound `E tr(B Hess u B Hess u) ≤ 2 tr(B²)`
for every real symmetric `B`. The hypotheses are exactly those of the witness producer. -/
theorem FunctionalInequalities.Analysis.exists_regular_moment_hessian_trace_bound :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace) := by
  obtain ⟨u, L, _LF, _T, hCanonical⟩ := exists_regular_moment_weak_stein_coupling
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hT25 := hCanonical.1.1.2
  obtain ⟨hbase, _hcutoffs⟩ := hCanonical.1.1.1.1.1.1
  obtain ⟨hc, hl, hnrm, hm, hC1, hG, _hF, _hw, hdata, _hT, _he,
    _hfirst, _hInv, hmean, _hq, _hflux, _hweighted, _hbounded⟩ := hbase
  exact ⟨u, L, hc, hl, hnrm, hm, hC1, hG, hdata, hmean, hT25⟩
end
end RegularMomentHessianTraceBound
end
end RegularSource
end

section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology
section
set_option maxHeartbeats 500000 in
theorem FunctionalInequalities.Probability.symmetric_matrix_variance_bound_of_isUnit {n : ℕ}
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))
    (C : ℝ)
    (hBound : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm → IsUnit B →
      ProbabilityTheory.variance (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, ∑ j, B i j * x i * x j) (mu : Measure _) ≤ C * (B * B).trace) :
    ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
      ProbabilityTheory.variance (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, ∑ j, B i j * x i * x j) (mu : Measure _) ≤ C * (B * B).trace := by
  intro B hB
  obtain ⟨seq, hunit, hlim⟩ := Analysis.exists_symmetric_isUnit_matrix_sequence_readable B hB
  have hvar := tendsto_variance_quadratic_matrix_forms_readable mu h4 hlim
  have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => C * (M * M).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  have hright := hcont.continuousAt.tendsto.comp hlim
  exact le_of_tendsto_of_tendsto hvar hright
    (Filter.Eventually.of_forall fun k => hBound (seq k) (hunit k).1 (hunit k).2)
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.variance_quadratic_le_smoothedLaw {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : ProbabilityMeasure E) (h4 : MemLp (id : E → E) 4 (mu : Measure E))
    (A : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    variance (fun x : E => ⟪A x,x⟫) (mu : Measure E) ≤
      variance (fun x : E => ⟪A x,x⟫) (smoothedLaw (mu : Measure E) s) := by
  let noise : ProbabilityMeasure E := ⟨gaussianLaw s,gaussianLaw_probability hs⟩
  exact Probability.quadratic_variance_le_centered_noise_convolution_readable mu noise h4
    (gaussianLaw_memLp_four hs) (gaussianLaw_mean_zero_readable hs) A
end
end
noncomputable section
open Filter
open scoped Topology
section
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.le_of_forall_inverse_noise_quadratic_error (a b c d : ℝ)
    (h : ∀ s : ℝ, 0 < s → a ≤ b + c * (2*s)⁻¹ + d * ((2*s)⁻¹)^2) : a ≤ b := by
  have hden : Tendsto (fun s : ℝ => 2*s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have heps : Tendsto (fun s : ℝ => (2*s)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp hden
  have hr : Tendsto (fun s : ℝ => b + c * (2*s)⁻¹ + d * ((2*s)⁻¹)^2) atTop (𝓝 b) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul heps)).add
      (tendsto_const_nhds.mul (heps.pow 2))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hr (Filter.eventually_atTop.2 ⟨1,fun s hs => h s (lt_of_lt_of_le zero_lt_one hs)⟩)
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
theorem FunctionalInequalities.Probability.Stein.quadratic_matrix_sum_eq_inner_action {n : ℕ} (A : KernelMatrix n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, A i j*x i*x j) = ⟪action A x,x⟫ := by
  simp only [action,PiLp.inner_apply,Real.inner_apply,Matrix.mulVec,dotProduct]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem FunctionalInequalities.Probability.Stein.inner_action_sandwich {n : ℕ} (S Q : KernelMatrix n) (hS : S.IsSymm)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪action Q (action S x),action S x⟫ = ⟪action (S*Q*S) x,x⟫ := by
  simp only [action_mul]
  exact inner_action_swap S (fun i j => congrFun (congrFun hS j) i)
    (action Q (action S x)) x
theorem FunctionalInequalities.Probability.Stein.latent_field_eq_action_conjugation {n : ℕ} (S H : KernelMatrix n)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap)
    (hself : IsSelfAdjoint e.toContinuousLinearMap)
    (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    e (action H (e.toContinuousLinearMap.adjoint v)) + t • v =
      action (S*H*S + t • (1 : KernelMatrix n)) v := by
  rw [hself.adjoint_eq]
  change e.toContinuousLinearMap (action H (e.toContinuousLinearMap v)) + t • v = _
  rw [he]
  simp only [action_add,action_smul,action_one,action_mul]
  rfl
theorem FunctionalInequalities.Probability.Stein.variance_quadratic_map_sandwich {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (S Q : KernelMatrix n) (hS : S.IsSymm) :
    variance (fun x => ⟪action Q x,x⟫) (μ.map (Matrix.toEuclideanLin S).toContinuousLinearMap) =
      variance (fun x => ⟪action (S*Q*S) x,x⟫) μ := by
  have hq : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪action Q x,x⟫) :=
    (Matrix.toEuclideanLin Q).toContinuousLinearMap.continuous.inner continuous_id
  rw [variance_map hq.measurable.aemeasurable
    (Matrix.toEuclideanLin S).toContinuousLinearMap.continuous.measurable.aemeasurable]
  exact variance_congr (ae_of_all _ fun x => inner_action_sandwich S Q hS x)
end
end
end

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped ContDiff RealInnerProductSpace Topology MatrixOrder
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 1500000 in
theorem solution :
    ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
      variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j*x i*x j)
        (μ : Measure _) ≤ 8 * Matrix.trace (M*M) := by
  obtain ⟨u,L,_hconv,hl,hnrm,hm,hC1,hG,hdata,hmean,hT25⟩ :=
    FunctionalInequalities.Analysis.exists_regular_moment_hessian_trace_bound hn hκ hK hKc hKint hW hstrong μ hμ hiso
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E := volume.tilted (-u)
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnrm]; norm_num)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hexp
  have hgnorm (x : E) : ‖gradient u x‖ ≤ (L : ℝ) := by
    calc
      _ = ‖fderiv ℝ u x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ hl
  have hu4 : MemLp (gradient u) 4 ρ := MemLp.of_bound
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hC1).aestronglyMeasurable (L : ℝ) (ae_of_all _ hgnorm)
  have hLC : FunctionalInequalities.KLS.LogConcave μ := FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_regularClass_readable μ
    hK.isClosed hKc hW.continuous hκ hstrong hμ
  have hfull : FunctionalInequalities.Probability.affineSupport μ = ⊤ := hiso.affineSupport_eq_top
  have hSmooth (e : E ≃L[ℝ] E) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q)
      (s : ℝ) (hs : 0 < s) :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_smoothed_quadratic_variance_le_latent_energy_readable μ hLC hfull hC1 hl hG hnrm hm e Q hQ hs
  have hμ4 : MemLp id 4 (μ : Measure E) := by
    rw [← hm]
    exact (memLp_map_measure_iff continuous_id.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hC1).measurable.aemeasurable).2 hu4
  apply FunctionalInequalities.Probability.symmetric_matrix_variance_bound_of_isUnit μ hμ4 8
  intro M hM hunit
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  obtain ⟨_,hSp,_,_,_,hSQS,_,_,hQL,e,he,hSelf⟩ := FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_readable M hM hunit
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hSp.isHermitian
  let QL : E →L[ℝ] E := (Matrix.toEuclideanLin Q).toContinuousLinearMap
  let μe := FunctionalInequalities.Probability.mapContinuousLinearEquiv μ e
  have hμe4 : MemLp id 4 (μe : Measure E) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.map_linear_memLp_four (μ : Measure E) e.toContinuousLinearMap hμ4
  have hvarmap : variance (fun x : E => ⟪QL x,x⟫) (μe : Measure E) =
      variance (fun x : E => ∑ i, ∑ j, M i j*x i*x j) (μ : Measure E) := by
    change variance (fun x => ⟪FunctionalInequalities.Probability.Stein.action Q x,x⟫) ((μ : Measure E).map e.toContinuousLinearMap) = _
    rw [he,FunctionalInequalities.Probability.Stein.variance_quadratic_map_sandwich _ S Q hS,hSQS]
    exact variance_congr (ae_of_all _ fun x => (FunctionalInequalities.Probability.Stein.quadratic_matrix_sum_eq_inner_action M x).symm)
  apply FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.le_of_forall_inverse_noise_quadratic_error
    (variance (fun x : E => ∑ i, ∑ j, M i j*x i*x j) (μ : Measure E))
    (8*Matrix.trace (M*M)) (8*Matrix.trace B) (4*(n : ℝ))
  intro s hs
  let γ : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let : IsProbabilityMeasure γ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  let P := ρ.prod γ
  have hHsym : ∀ᵐ y ∂ρ, (FunctionalInequalities.Probability.Stein.hessianMatrix u y).IsSymm := by
    filter_upwards [(tilted_absolutelyContinuous (volume : Measure E) (-u)).ae_le hdata] with y hy
    exact Matrix.isHermitian_iff_isSymm.mp hy.1.isHermitian
  have hEn := FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le_readable ρ γ (FunctionalInequalities.Probability.Stein.hessianMatrix u)
    (fun i j => FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u i j) hHsym
    (fun i j => (hmean i j).1) (fun i j => (hmean i j).2) hT25 M hM hunit ((2*s)⁻¹)
  have hEnergy : (∑ i : Fin n, ∫ p : E × E,
      ‖e (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (e.toContinuousLinearMap.adjoint
        (QL (EuclideanSpace.single i 1)))) + (2*s)⁻¹ • QL (EuclideanSpace.single i 1)‖^2 ∂P) ≤
      2*Matrix.trace (M*M) + 2*(2*s)⁻¹*Matrix.trace B + (n : ℝ)*((2*s)⁻¹)^2 := by
    calc
      _ = ∑ i : Fin n, ∫ p : E × E,
          ‖FunctionalInequalities.Probability.Stein.action (S*FunctionalInequalities.Probability.Stein.hessianMatrix u p.1*S + (2*s)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))
            (FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1))‖^2 ∂P := by
        apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        exact ae_of_all _ fun p => congrArg (fun v : E => ‖v‖^2)
          (FunctionalInequalities.Probability.Stein.latent_field_eq_action_conjugation S (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) e he hSelf
            ((2*s)⁻¹) (FunctionalInequalities.Probability.Stein.action Q (EuclideanSpace.single i 1)))
      _ ≤ _ := hEn.2
  have hSM := hSmooth e QL hQL s hs
  calc
    _ = variance (fun x : E => ⟪QL x,x⟫) (μe : Measure E) := hvarmap.symm
    _ ≤ variance (fun x : E => ⟪QL x,x⟫) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw (μe : Measure E) s) :=
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.variance_quadratic_le_smoothedLaw μe hμe4 QL hs
    _ ≤ 4 * ∑ i : Fin n, ∫ p : E × E,
        ‖e (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (e.toContinuousLinearMap.adjoint
          (QL (EuclideanSpace.single i 1)))) + (2*s)⁻¹ • QL (EuclideanSpace.single i 1)‖^2 ∂P := hSM
    _ ≤ 4 * (2*Matrix.trace (M*M) + 2*(2*s)⁻¹*Matrix.trace B + (n : ℝ)*((2*s)⁻¹)^2) :=
      mul_le_mul_of_nonneg_left hEnergy (by norm_num)
    _ = _ := by ring
