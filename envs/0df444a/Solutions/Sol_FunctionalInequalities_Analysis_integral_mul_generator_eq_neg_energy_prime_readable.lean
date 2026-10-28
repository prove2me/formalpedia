-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_prime_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:28.977427+00:00
-- url     : https://prove2.me/submissions/69aed847-cf1b-40b6-9385-7208f8e683c0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
import Theorems.Thm_FunctionalInequalities_Analysis_assemble_generator_readable
import Theorems.Thm_FunctionalInequalities_Analysis_smooth_test_derivative_readable

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

noncomputable section
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Analysis.continuous_coord {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (FunctionalInequalities.Analysis.coord f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
private lemma FunctionalInequalities.Analysis.continuous_coord_of_lipschitz_gradient {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : LipschitzWith L (gradient f)) (i : Fin n) :
    Continuous (FunctionalInequalities.Analysis.coord f i) := by
  change Continuous
    (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))
  simpa [Function.comp_def, inner_gradient_left] using
    ((((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)).lipschitz.comp
      hf).continuous)
private lemma FunctionalInequalities.Analysis.integrable_energy {n : ℕ}
    {u F a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (ha : ∀ i, Continuous (FunctionalInequalities.Analysis.coord a i))
    (hf : ∀ j, Continuous (FunctionalInequalities.Analysis.coord f j))
    (hc : ∀ i j, HasCompactSupport
      (fun x => FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x))) :
    Integrable (FunctionalInequalities.Analysis.energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hi (i j : Fin n) :
      Integrable
        (fun x => (hessianMatrix u x)⁻¹ i j *
          (FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hcont : Continuous
        (fun x => FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x)) :=
      ((ha i).mul (hf j)).mul
        (Real.continuous_exp.comp hu.continuous.neg)
    obtain ⟨C, hC⟩ := (hc i j).exists_bound_of_continuous hcont
    exact integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
      hG hF hdet hcont.measurable (hc i j) hC i j
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  have he :
      (fun x => ∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
        (FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x))) =
        FunctionalInequalities.Analysis.energyDensity u a f := by
    funext x
    simp only [FunctionalInequalities.Analysis.energyDensity, Finset.sum_mul, mul_assoc]
  rw [he] at hs
  exact hs
private lemma FunctionalInequalities.Analysis.energy_swap {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) :
    FunctionalInequalities.Analysis.energyDensity u a f =ᵐ[volume] FunctionalInequalities.Analysis.energyDensity u f a := by
  classical
  filter_upwards [hG.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hA := (hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx).inv
  have hs (i j : Fin n) :
      (hessianMatrix u x)⁻¹ j i = (hessianMatrix u x)⁻¹ i j := by
    simpa only [star_trivial] using hA.apply i j
  unfold FunctionalInequalities.Analysis.energyDensity
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs i j]
  ring
/-- The same identity with the roles exchanged (`η` inside the generator, `w` outside). -/
theorem solution {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, w x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hηfd : ContDiff ℝ 1 (fderiv ℝ η) :=
    hη.fderiv_right (by norm_num)
  have ht (i : Fin n) :
      ∃ L : NNReal, LipschitzWith L (FunctionalInequalities.Analysis.weightedTest u w η i) ∧
        HasCompactSupport (FunctionalInequalities.Analysis.weightedTest u w η i) := by
    have hc : HasCompactSupport (FunctionalInequalities.Analysis.weightedTest u w η i) :=
      (hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_left
    have hd : ContDiff ℝ 1 (FunctionalInequalities.Analysis.weightedTest u w η i) :=
      (hw.mul hu.neg.exp).mul (hηfd.clm_apply contDiff_const)
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hd one_ne_zero
    exact ⟨L, hL, hc⟩
  have hd (i : Fin n) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
        FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u w η i) j x =
          Real.exp (-u x) *
            (FunctionalInequalities.Analysis.coord w j x * FunctionalInequalities.Analysis.coord η i x -
              w x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord η i x +
              w x * FunctionalInequalities.Probability.Stein.hessianMatrix η x j i) :=
    Eventually.of_forall (fun x j => FunctionalInequalities.Analysis.smooth_test_derivative_readable hu hw hη i j x)
  have hE : Integrable (FunctionalInequalities.Analysis.energyDensity u w η)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply FunctionalInequalities.Analysis.integrable_energy hu hG hF.continuous hdet
      (FunctionalInequalities.Analysis.continuous_coord_of_lipschitz_gradient hGw) (FunctionalInequalities.Analysis.continuous_coord hη1)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).mul_left :
        HasCompactSupport (fun x => FunctionalInequalities.Analysis.coord w i x * FunctionalInequalities.Analysis.coord η j x)).mul_right
  change (∫ x, FunctionalInequalities.Analysis.generatorDensity u V w η x) =
    -∫ x, FunctionalInequalities.Analysis.energyDensity u η w x
  calc
    (∫ x, FunctionalInequalities.Analysis.generatorDensity u V w η x) =
        -∫ x, FunctionalInequalities.Analysis.energyDensity u w η x :=
      FunctionalInequalities.Analysis.assemble_generator_readable hu hG hV hF hdet ht hd hE
    _ = -∫ x, FunctionalInequalities.Analysis.energyDensity u η w x := by
      rw [integral_congr_ae (FunctionalInequalities.Analysis.energy_swap (a := w) (f := η) hu hG)]
