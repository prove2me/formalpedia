-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_pairings_integrable_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:13.858745+00:00
-- url     : https://prove2.me/submissions/c1fd56a7-f9c5-4b92-8b79-d2b4b93a2bc8

import Definitions.Def_KLSModular_FunctionalInequalities_L2_Pairing
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable

section
open MeasureTheory Filter
open scoped RealInnerProductSpace Topology
section
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : MeasureTheory.Measure A}
/-- The pointwise pairing of two `L²` fields is integrable. -/
theorem FunctionalInequalities.L2.integrable_inner_of_memLp {a f : A → E}
    (ha : MemLp a 2 μ) (hf : MemLp f 2 μ) : Integrable (fun x => ⟪a x, f x⟫) μ := by
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (ha.toLp a) (hf.toLp f)).congr
  filter_upwards [ha.coeFn_toLp, hf.coeFn_toLp] with x hax hfx
  rw [hax, hfx]
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
omit [CompleteSpace E] in
/-- `γ_s` has a finite second moment. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs
end InnerProduct
end StructuredSpace
end WeakThirdDerivativeSymmetry
section GradientDerivativeIdentification
open FunctionalInequalities.Analysis
section
/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx
end
end GradientDerivativeIdentification
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
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section
section
theorem FunctionalInequalities.Probability.Stein.memLp_hessian_action_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (mu : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure mu]
    (v : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun y => action (hessianMatrix u y) v) 2 mu := by
  classical
  apply MemLp.of_eval_piLp
  intro i
  change MemLp (fun y => ∑ j, hessianMatrix u y i j * v j) 2 mu
  apply memLp_finsetSum Finset.univ
  intro j _
  have hij : MemLp (fun y => hessianMatrix u y i j) 2 mu :=
    MemLp.of_bound (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
      (G : ℝ) (ae_of_all _ fun y => norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable hG y i j)
  exact hij.mul_const (v j)
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 800000 in
theorem solution {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    let Z := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => S (gradient u p.1) + p.2
    let F := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint v))
    MemLp Z 2 P ∧ MemLp F 2 P ∧ MemLp (fun p => gradient h (Z p)) 2 P ∧
    Integrable (fun p => ⟪S (gradient u p.1),v⟫ * h (Z p)) P ∧
    Integrable (fun p => ⟪p.2,v⟫ * h (Z p)) P ∧
    Integrable (fun p => ⟪S.adjoint v,FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫) P ∧
    Integrable (fun p => fderiv ℝ h (Z p) v) P := by
  let E := EuclideanSpace ℝ (Fin n)
  let rho : Measure E := volume.tilted (-u)
  let nu : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let P := rho.prod nu
  let Z : E × E → E := fun p => S (gradient u p.1) + p.2
  let F : E × E → E := fun p => S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint v))
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hexp
  let : IsProbabilityMeasure nu := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hgnorm (f : E → ℝ) {K : NNReal} (hf : LipschitzWith K f) (x : E) :
      ‖gradient f x‖ ≤ (K : ℝ) := by
    calc
      ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
        (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ hf
  have hu2 : MemLp (gradient u) 2 rho := MemLp.of_bound
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu).aestronglyMeasurable (L : ℝ) (ae_of_all _ (hgnorm u hL))
  have hSU : MemLp (fun p : E × E => S (gradient u p.1)) 2 P :=
    (hu2.continuousLinearMap_comp S).comp_fst nu
  have hnoise : MemLp (fun p : E × E => p.2) 2 P :=
    (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).comp_snd rho
  have hZ2 : MemLp Z 2 P := hSU.add hnoise
  have hZmeas : Measurable Z :=
    (S.continuous.measurable.comp ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu).measurable.comp measurable_fst)).add measurable_snd
  have hh2 : MemLp (fun p => h (Z p)) 2 P := MemLp.of_bound
    (hh.continuous.measurable.comp hZmeas).aestronglyMeasurable C (ae_of_all _ fun p => hbound (Z p))
  have hg2 : MemLp (fun p => gradient h (Z p)) 2 P := MemLp.of_bound
    ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hh).measurable.comp hZmeas).aestronglyMeasurable
      (Lh : ℝ) (ae_of_all _ fun p => hgnorm h hhLip (Z p))
  have hF2 : MemLp F 2 P :=
    ((FunctionalInequalities.Probability.Stein.memLp_hessian_action_of_lipschitz_gradient hG rho (S.adjoint v)).continuousLinearMap_comp S).comp_fst nu
  have hSL : Integrable (fun p : E × E => ⟪S (gradient u p.1),v⟫ * h (Z p)) P :=
    (hSU.inner_const (𝕜 := ℝ) v).integrable_mul hh2
  have hNL : Integrable (fun p : E × E => ⟪p.2,v⟫ * h (Z p)) P :=
    (hnoise.inner_const (𝕜 := ℝ) v).integrable_mul hh2
  have hdiff : ∀ᵐ y ∂rho, DifferentiableAt ℝ (gradient u) y :=
    (tilted_absolutelyContinuous (volume : Measure E) (-u)).ae_le
      (hG.ae_differentiableAt (μ := volume))
  have hSym : ∀ᵐ y ∂rho, (FunctionalInequalities.Probability.Stein.hessianMatrix u y).IsHermitian :=
    hdiff.mono fun y hy => FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient hu hy
  have hproj : MeasurePreserving (Prod.fst : E × E → E) P rho := measurePreserving_fst
  have hSR : Integrable (fun p : E × E =>
      ⟪S.adjoint v,FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫) P := by
    apply (FunctionalInequalities.L2.integrable_inner_of_memLp hF2 hg2).congr
    filter_upwards [hproj.quasiMeasurePreserving.ae hSym] with p hp
    change ⟪S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint v)),gradient h (Z p)⟫ = _
    rw [← S.adjoint_inner_right]
    exact (FunctionalInequalities.Probability.Stein.inner_action_swap (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1)
      (fun i j => by simpa only [star_trivial] using hp.apply j i)
      (S.adjoint v) (S.adjoint (gradient h (Z p)))).symm
  have hNR : Integrable (fun p : E × E => fderiv ℝ h (Z p) v) P := by
    apply ((hg2.inner_const (𝕜 := ℝ) v).integrable one_le_two).congr
    exact ae_of_all _ fun p => inner_gradient_left
  exact ⟨hZ2,hF2,hg2,hSL,hNL,hSR,hNR⟩
