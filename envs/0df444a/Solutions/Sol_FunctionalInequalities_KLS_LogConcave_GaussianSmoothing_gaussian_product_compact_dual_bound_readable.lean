-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_compact_dual_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:24:07.887363+00:00
-- url     : https://prove2.me/submissions/92d622fd-d2ac-4302-a661-9f2287937f6a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_latent_map_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_source_stein_identity_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_source_stein_pairings_integrable_readable
import Theorems.Thm_FunctionalInequalities_Probability_Stein_compact_linear_pairing_sq_le_of_source_identity_readable

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

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 800000 in
theorem solution {n : ℕ}
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hsource : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map
      (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s)
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ((μ : Measure _).map S) s)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    (∫ x, ⟪x,v⟫ * h x ∂(ν : Measure _)) ^ 2 ≤
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint v)) + (2*s)⁻¹ • v‖ ^ 2 ∂P) *
      ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E := volume.tilted (-u)
  let γ : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let P := ρ.prod γ
  let Z : E × E → E := fun p => S (gradient u p.1) + p.2
  let F : E × E → E := fun p => S (FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint v)) + (2*s)⁻¹ • v
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hexp
  let : IsProbabilityMeasure γ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hh1 : ContDiff ℝ 1 h := hh.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Lh,hhLip⟩ := FunctionalInequalities.Energy.WeightedGradient.lipschitzWith_of_contDiff_hasCompactSupport hh hhc
  obtain ⟨C,hC⟩ := hh.continuous.bounded_above_of_compact_support hhc
  have hZ : Measurable Z :=
    (S.continuous.measurable.comp ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu).measurable.comp measurable_fst)).add measurable_snd
  have hmap : P.map Z = (ν : Measure E) :=
    (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_latent_map_readable ρ (μ : Measure E) (gradient u)
      (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hu).measurable hsource S hs).trans hν.symm
  obtain ⟨_,hF2,_,_,_,_,_⟩ :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_pairings_integrable_readable hu hL hG hnorm hh1 hhLip C hC S v hs
  have hF : MemLp F 2 P := hF2.add (memLp_const ((2*s)⁻¹ • v))
  have hpair := (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_identity_readable hu hL hG hnorm hh1 hhLip C hC S v hs).2.2
  have hdiff : ∀ᵐ y ∂ρ, DifferentiableAt ℝ (gradient u) y :=
    (tilted_absolutelyContinuous (volume : Measure E) (-u)).ae_le
      (hG.ae_differentiableAt (μ := volume))
  have hSym : ∀ᵐ y ∂ρ, (FunctionalInequalities.Probability.Stein.hessianMatrix u y).IsHermitian := by
    filter_upwards [hdiff] with y hy
    exact FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient hu hy
  have hproj : MeasurePreserving (Prod.fst : E × E → E) P ρ := measurePreserving_fst
  have hright : (∫ p : E × E,
      ⟪S.adjoint v,FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫ +
        (2*s)⁻¹ * fderiv ℝ h (Z p) v ∂P) = ∫ p, ⟪F p,gradient h (Z p)⟫ ∂P := by
    apply integral_congr_ae
    filter_upwards [hproj.quasiMeasurePreserving.ae hSym] with p hp
    dsimp only [F]
    rw [inner_add_left,real_inner_smul_left]
    congr 1
    · rw [← S.adjoint_inner_right]
      exact FunctionalInequalities.Probability.Stein.inner_action_swap (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1)
        (fun i j => by simpa only [star_trivial] using hp.apply j i)
        (S.adjoint v) (S.adjoint (gradient h (Z p)))
    · rw [real_inner_comm (gradient h (Z p)) v,inner_gradient_left]
  have hid : (∫ x, ⟪x,v⟫ * h x ∂(ν : Measure E)) = ∫ p, ⟪F p,gradient h (Z p)⟫ ∂P := by
    calc
      _ = ∫ p, ⟪Z p,v⟫ * h (Z p) ∂P := by
        rw [← hmap]
        exact integral_map hZ.aemeasurable
          ((continuous_id.inner continuous_const).mul hh.continuous).aestronglyMeasurable
      _ = _ := hpair.trans hright
  exact FunctionalInequalities.Probability.Stein.compact_linear_pairing_sq_le_of_source_identity_readable P ν Z F hZ hmap hF v h hh hhc hid
