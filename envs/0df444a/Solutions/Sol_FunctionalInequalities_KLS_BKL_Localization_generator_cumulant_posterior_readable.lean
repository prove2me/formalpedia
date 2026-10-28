-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.generator_cumulant_posterior_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:27.461022+00:00
-- url     : https://prove2.me/submissions/f5ee5003-942e-42e5-9062-8fb0178120f4

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Positive
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact_readable
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_logLaplace_posterior_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_fderiv_logPartition_c_apply_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_logLaplace_compactPosterior_readable

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
open scoped ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem FunctionalInequalities.Analysis.directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))
private theorem FunctionalInequalities.Analysis.directional_two {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional [v, w] f x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const w)]
  simp
/-- Adjacent directional derivatives commute by genuine real C² symmetry. -/
theorem FunctionalInequalities.Analysis.directional_swap {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) (v w : E) :
    directional (v :: w :: hs) f = directional (w :: v :: hs) f := by
  funext x
  have hg := directional_contDiff hf hs
  have he (u t : E) : directional (u :: t :: hs) f x = directional [u,t] (directional hs f) x := rfl
  rw [he, he, directional_two hg, directional_two hg]
  exact hg.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) v w
/-- Full permutation symmetry follows from adjacent swaps; no tensor symmetry is a premise. -/
theorem FunctionalInequalities.Analysis.directional_perm {f : E → F} (hf : ContDiff ℝ ∞ f) {hs ks : List E}
    (h : hs.Perm ks) : directional hs f = directional ks f := by
  induction h with
  | nil => rfl
  | cons v h IH =>
    change (fun x => fderiv ℝ (directional _ f) x v) = (fun x => fderiv ℝ (directional _ f) x v)
    rw [IH]
  | swap v w hs => exact directional_swap hf hs w v
  | trans h1 h2 IH1 IH2 => exact IH1.trans IH2
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
end
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
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
section Calculus
variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_append (a b : List U) (f : U → ℝ) :
    directional (a ++ b) f = directional a (directional b f) := by
  induction a with
  | nil => rfl
  | cons u a ih =>
      simp only [List.cons_append, directional, ih]
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_comm {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (a b : List U) :
    directional a (directional b f) = directional b (directional a f) := by
  rw [← dir_append, ← dir_append]
  exact directional_perm hf List.perm_append_comm
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_affine {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : V →L[ℝ] U) (a : U) (l : List V) (x : V) :
    directional l (fun y => f (a + L y)) x =
      directional (l.map L) f (a + L x) := by
  induction l generalizing x with
  | nil => rfl
  | cons v l ih =>
      simp only [List.map_cons, directional]
      rw [show directional l (fun y => f (a + L y)) =
          (fun y => directional (l.map L) f (a + L y)) from funext ih]
      have hd := (directional_contDiff hf (l.map L)).differentiable
        (by simp) (a + L x)
      have he := (hd.hasFDerivAt.comp x
        (HasFDerivAt.const_add a L.hasFDerivAt)).fderiv
      convert congrArg (fun T : V →L[ℝ] ℝ => T v) he using 1 <;> rfl
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_add {f g : U → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (l : List U) (x : U) :
    directional l (fun y => f y + g y) x =
      directional l f x + directional l g x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
      change fderiv ℝ (directional l (fun y => f y + g y)) x u = _
      rw [show directional l (fun y => f y + g y) =
          (fun y => directional l f y + directional l g y) from funext ih]
      rw [fderiv_fun_add
        ((directional_contDiff hf l).differentiable (by simp) x)
        ((directional_contDiff hg l).differentiable (by simp) x)]
      rfl
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_mul {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (l : List U) (x : U) :
    directional l (fun y => c * f y) x = c * directional l f x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
      change fderiv ℝ (directional l (fun y => c * f y)) x u = _
      rw [show directional l (fun y => c * f y) =
          (fun y => c * directional l f y) from funext ih]
      rw [fderiv_const_mul
        ((directional_contDiff hf l).differentiable (by simp) x)]
      rfl
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_sum {d : ℕ} {f : Fin d → U → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (l : List U) (x : U) :
    directional l (fun y => ∑ i, f i y) x =
      ∑ i, directional l (f i) x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
      change fderiv ℝ (directional l (fun y => ∑ i, f i y)) x u = _
      rw [show directional l (fun y => ∑ i, f i y) =
          (fun y => ∑ i, directional l (f i) y) from funext ih]
      rw [fderiv_fun_sum (fun i _ =>
        (directional_contDiff (hf i) l).differentiable (by simp) x)]
      simp only [sum_apply, directional]
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_two {f : U → ℝ} (hf : ContDiff ℝ ∞ f)
    (u x : U) :
    directional [u, u] f x = fderiv ℝ (fderiv ℝ f) x u u := by
  change fderiv ℝ (fun y => fderiv ℝ f y u) x u = _
  rw [fderiv_clm_apply
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const u)]
  simp
private theorem FunctionalInequalities.KLS.BKL.Localization.smooth_right {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : U) :
    ContDiff ℝ ∞ (fun z => f (p, z)) := by
  have hmap : ContDiff ℝ ∞ (fun z : V => (p, z)) :=
    (contDiff_const (c := p)).prodMk contDiff_id
  convert hf.comp hmap using 1
  rfl
private theorem FunctionalInequalities.KLS.BKL.Localization.smooth_left {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : V) :
    ContDiff ℝ ∞ (fun p => f (p, z)) := by
  have hmap : ContDiff ℝ ∞ (fun p : U => (p, z)) :=
    contDiff_id.prodMk (contDiff_const (c := z))
  convert hf.comp hmap using 1
  rfl
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_right {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List V) (p : U) (z : V) :
    directional l (fun y => f (p, y)) z =
      directional (l.map (fun v => ((0 : U), v))) f (p, z) := by
  have he := dir_affine hf (ContinuousLinearMap.inr ℝ U V) (p, 0) l z
  have hmap : (⇑(ContinuousLinearMap.inr ℝ U V)) =
      (fun v : V => ((0 : U), v)) := by
    funext v
    rfl
  rw [hmap] at he
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using he
private theorem FunctionalInequalities.KLS.BKL.Localization.dir_left {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (l : List U) (p : U) (z : V) :
    directional l (fun q => f (q, z)) p =
      directional (l.map (fun u => (u, (0 : V)))) f (p, z) := by
  have he := dir_affine hf (ContinuousLinearMap.inl ℝ U V) (0, z) l p
  have hmap : (⇑(ContinuousLinearMap.inl ℝ U V)) =
      (fun u : U => (u, (0 : V))) := by
    funext u
    rfl
  rw [hmap] at he
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using he
private theorem FunctionalInequalities.KLS.BKL.Localization.fixedOp_slice {d : ℕ} {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : U) (s : Fin d → U) (p : U) (z : V) :
    FunctionalInequalities.KLS.BKL.Localization.fixedOp b s (fun q => f (q, z)) p =
      directional [(b, (0 : V))] f (p, z) +
        (1 / 2 : ℝ) * ∑ k,
          directional [(s k, (0 : V)), (s k, (0 : V))] f (p, z) := by
  unfold FunctionalInequalities.KLS.BKL.Localization.fixedOp
  have hfirst :
      fderiv ℝ (fun q => f (q, z)) p b =
        directional [(b, (0 : V))] f (p, z) := by
    simpa only [List.map_cons, List.map_nil, directional] using
      dir_left hf [b] p z
  have hsecond (k : Fin d) :
      fderiv ℝ (fderiv ℝ (fun q => f (q, z))) p (s k) (s k) =
        directional [(s k, (0 : V)), (s k, (0 : V))] f (p, z) := by
    rw [← dir_two (smooth_left hf z)]
    simpa only [List.map_cons, List.map_nil] using dir_left hf [s k, s k] p z
  simp only [hfirst, hsecond]
private theorem FunctionalInequalities.KLS.BKL.Localization.fixedOp_iterated {d m : ℕ} {f : U × V → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : U) (s : Fin d → U)
    (p : U) (h : Fin m → V) :
    FunctionalInequalities.KLS.BKL.Localization.fixedOp b s (fun q => iteratedFDeriv ℝ m (fun z => f (q, z)) 0 h) p =
      iteratedFDeriv ℝ m (fun z => FunctionalInequalities.KLS.BKL.Localization.fixedOp b s (fun q => f (q, z)) p) 0 h := by
  let l : List (U × V) := (List.ofFn h).map (fun v => ((0 : U), v))
  let g : U × V → ℝ := directional l f
  have hg : ContDiff ℝ ∞ g := directional_contDiff hf l
  let a : U × V → ℝ := directional [(b, (0 : V))] f
  let t : Fin d → U × V → ℝ :=
    fun k => directional [(s k, (0 : V)), (s k, (0 : V))] f
  have ha : ContDiff ℝ ∞ a := directional_contDiff hf _
  have ht (k : Fin d) : ContDiff ℝ ∞ (t k) := directional_contDiff hf _
  have hsum : ContDiff ℝ ∞ (fun x => ∑ k, t k x) :=
    ContDiff.sum (fun k _ => ht k)
  let H : U × V → ℝ := fun x => a x + (1 / 2 : ℝ) * ∑ k, t k x
  have hH : ContDiff ℝ ∞ H :=
    ha.add (contDiff_const.mul hsum)
  have hjet :
      (fun q => iteratedFDeriv ℝ m (fun z => f (q, z)) 0 h) =
        (fun q => g (q, 0)) := by
    funext q
    rw [← directional_ofFn (smooth_right hf q), dir_right hf]
  have hop :
      (fun z => FunctionalInequalities.KLS.BKL.Localization.fixedOp b s (fun q => f (q, z)) p) =
        (fun z => H (p, z)) := by
    funext z
    exact fixedOp_slice hf b s p z
  rw [hjet, hop, fixedOp_slice hg,
    ← directional_ofFn (smooth_right hH p), dir_right hH]
  change directional [(b, (0 : V))] (directional l f) (p, 0) +
      (1 / 2 : ℝ) * ∑ k,
        directional [(s k, (0 : V)), (s k, (0 : V))]
          (directional l f) (p, 0) =
    directional l (fun x => a x + (1 / 2 : ℝ) * ∑ k, t k x) (p, 0)
  rw [dir_add ha (contDiff_const.mul hsum), dir_mul hsum, dir_sum ht]
  congr 1
  · exact congrFun (dir_comm hf _ l) (p, 0)
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (dir_comm hf _ l) (p, 0)
end Calculus
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 2000000 in
/-- **BKL Lemma 4.3, (73), in generator form**: for `m ≥ 3`, every slot `i₀` and directions `h`, the generator of
(67) applied to the posterior cumulant `p ↦ κ_m(μ_p)(h)` is `−(m κ_m(h) + L_m(h))`, where `L_m` is the middle term
(72) taken at the slot `i₀`. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) {m : ℕ} (hm : 3 ≤ m)
    (h : Fin m → EuclideanSpace ℝ (Fin n)) (i₀ : Fin m) (p : FunctionalInequalities.KLS.BKL.Localization.Param n) :
    FunctionalInequalities.KLS.BKL.Localization.generator μ hc
        (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p =
      -((m : ℝ) * FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) m h +
        FunctionalInequalities.KLS.BKL.lowerDrift (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) h i₀) := by
  classical
  let F : FunctionalInequalities.KLS.BKL.Localization.Param n × EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
    FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc r.1.1 r.1.2 :
      Measure (EuclideanSpace ℝ (Fin n))) r.2
  have hF : ContDiff ℝ ∞ F := by
    have hmap : ContDiff ℝ ∞
        (fun r : FunctionalInequalities.KLS.BKL.Localization.Param n × EuclideanSpace ℝ (Fin n) =>
          ((r.1.1 + r.2, r.1.2) : FunctionalInequalities.KLS.BKL.Localization.Param n)) :=
      ((contDiff_fst.fst).add contDiff_snd).prodMk contDiff_fst.snd
    have h₁ : ContDiff ℝ ∞
        (fun r : FunctionalInequalities.KLS.BKL.Localization.Param n × EuclideanSpace ℝ (Fin n) =>
          FunctionalInequalities.Probability.Posterior.logPartition μ (r.1.1 + r.2) r.1.2) := by
      convert (FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable μ hc).comp hmap using 1
      rfl
    have h₂ : ContDiff ℝ ∞
        (fun r : FunctionalInequalities.KLS.BKL.Localization.Param n × EuclideanSpace ℝ (Fin n) =>
          FunctionalInequalities.Probability.Posterior.logPartition μ r.1.1 r.1.2) := by
      convert (FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable μ hc).comp contDiff_fst using 1
      rfl
    have heq : F = fun r =>
        FunctionalInequalities.Probability.Posterior.logPartition μ (r.1.1 + r.2) r.1.2 - FunctionalInequalities.Probability.Posterior.logPartition μ r.1.1 r.1.2 := by
      funext r
      exact FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable μ hc r.1.1 r.1.2 r.2
    rw [heq]
    exact h₁.sub h₂
  let ν := FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2
  have hν : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support := by
    dsimp only [ν]
    rw [FunctionalInequalities.Probability.Posterior.compactPosterior_support]
    exact hc
  let Λ := FunctionalInequalities.Analysis.BakryEmery.logLaplace (ν : Measure (EuclideanSpace ℝ (Fin n)))
  have hΛ : ContDiff ℝ ∞ Λ :=
    FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace _ (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hν)
  have hlog : Λ = fun z =>
      FunctionalInequalities.Probability.Posterior.logPartition μ (p.1 + z) p.2 - FunctionalInequalities.Probability.Posterior.logPartition μ p.1 p.2 := by
    funext z
    exact FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable μ hc p.1 p.2 z
  have hgrad (z : EuclideanSpace ℝ (Fin n)) :
      gradient Λ z = FunctionalInequalities.Probability.Posterior.posteriorMean μ (p.1 + z) p.2 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_gradient_left, hlog, fderiv_sub_const]
    rw [fderiv_comp_add_left (f := fun y => FunctionalInequalities.Probability.Posterior.logPartition μ y p.2) p.1]
    rw [FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply_readable μ hc]
    exact (real_inner_comm w (FunctionalInequalities.Probability.Posterior.posteriorMean μ (p.1 + z) p.2)).symm
  have hg : ContDiff ℝ ∞ (gradient Λ) := by
    let T : ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv
    exact T.contDiff.comp (hΛ.fderiv_right (by simp))
  let v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => gradient Λ z - gradient Λ 0
  let R : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ⟪v z, Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (v z)⟫
  have hv : ContDiff ℝ ∞ v := hg.sub contDiff_const
  have hR : ContDiff ℝ ∞ R :=
    hv.inner ℝ ((Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p)).contDiff.comp hv)
  have h71 :
      (fun z => FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun q => F (q, z)) p) =
        (fun z => -(1 / 2 : ℝ) * R z) := by
    funext z
    simpa only [F, FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable, R, v, hgrad, add_zero] using
      FunctionalInequalities.KLS.BKL.Localization.generator_logLaplace_posterior_readable μ hc hiso z p
  change FunctionalInequalities.KLS.BKL.Localization.fixedOp (FunctionalInequalities.KLS.BKL.Localization.drift μ hc p) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p)
      (fun q => iteratedFDeriv ℝ m (fun z => F (q, z)) 0 h) p = _
  rw [FunctionalInequalities.KLS.BKL.Localization.fixedOp_iterated hF]
  change iteratedFDeriv ℝ m
      (fun z => FunctionalInequalities.KLS.BKL.Localization.generator μ hc (fun q => F (q, z)) p) 0 h = _
  rw [h71]
  have hscale :
      iteratedFDeriv ℝ m (fun z => -(1 / 2 : ℝ) * R z) 0 h =
        -(1 / 2 : ℝ) * iteratedFDeriv ℝ m R 0 h := by
    have hRm : ContDiffAt ℝ m R 0 :=
      (hR.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hs : iteratedFDeriv ℝ m (fun z => (-(1 / 2 : ℝ)) • R z) 0 =
        (-(1 / 2 : ℝ)) • iteratedFDeriv ℝ m R 0 :=
      iteratedFDeriv_const_smul_apply' hRm
    simpa only [smul_eq_mul, smul_apply] using
      congrArg (fun T => T h) hs
  rw [hscale]
  have hgroup :
      iteratedFDeriv ℝ m R 0 h =
        (2 * (m : ℝ)) * FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m h +
          2 * FunctionalInequalities.KLS.BKL.lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) h i₀ := by
    exact FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact_readable ν hν
      (FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2) hm h i₀
  rw [hgroup]
  change -(1 / 2 : ℝ) *
      ((2 * (m : ℝ)) * FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m h +
        2 * FunctionalInequalities.KLS.BKL.lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) h i₀) =
    -((m : ℝ) * FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m h +
        FunctionalInequalities.KLS.BKL.lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) h i₀)
  ring
