-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:33.789446+00:00
-- url     : https://prove2.me/submissions/7734d132-5827-4fad-8b26-5d4420eb888d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_lipschitzWith_smul_of_locallyLipschitz_readable
import Theorems.Thm_FunctionalInequalities_Analysis_assemble_generator_readable

noncomputable section
section WeightedGradientTest
open scoped RealInnerProductSpace ContDiff
section
/-- Compactly supported weighted derivative test for the weak Letwin generator identity.
No global bound on the gradient of w is assumed. -/
private theorem FunctionalInequalities.Analysis.exists_lipschitz_compact_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∃ L : NNReal,
      LipschitzWith L (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) ∧
      HasCompactSupport (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  let γ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => η x * Real.exp (-u x)
  have hγ : ContDiff ℝ 1 γ := hη.mul hu.neg.exp
  have hγc : HasCompactSupport γ := hηc.mul_right
  obtain ⟨Kγ, hKγ⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hγc hγ one_ne_zero
  let e : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ i
  have hcoord :
      LipschitzWith (‖(innerSL ℝ) e‖₊ * Gw)
        (fun x => fderiv ℝ w x e) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) e).lipschitz.comp hGw)
  obtain ⟨⟨L, hL⟩, _⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_readable
      hKγ hγc hcoord.locallyLipschitz
  refine ⟨L, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hL
  · exact hγc.mul_right
end
end WeightedGradientTest
section WeightedGradientTestDerivative
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff
section
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'
/-- Almost-everywhere derivative of the actual weighted gradient test for Letwin (2.2).
Only C1 u and eta and a Lipschitz gradient of w are needed. -/
private theorem FunctionalInequalities.Analysis.ae_fderiv_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        Real.exp (-u x) *
          (fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
            η x * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            η x * hessianMatrix w x j i) := by
  filter_upwards [hGw.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hux : DifferentiableAt ℝ u x :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hηx : DifferentiableAt ℝ η x :=
    (hη.differentiable one_ne_zero).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ w) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent :
      DifferentiableAt ℝ
        (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    hfd.clm_apply hc
  have he :
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x =
      (η x * Real.exp (-u x)) •
          fderiv ℝ
            (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x +
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) •
          (η x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
            Real.exp (-u x) • fderiv ℝ η x) :=
    ((hηx.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  intro j
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  rw [hessian_coord_of_gradient_diff (i := j) (j := i) hx]
  ring
end
end WeightedGradientTestDerivative
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
section
private lemma FunctionalInequalities.Analysis.continuous_coord {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (FunctionalInequalities.Analysis.coord f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
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
end
end GeneratorIdentities
section C1GeneratorTestReuse
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
/-- C1 compact multiplier version of the closed weak generator identity.
Weak-source support for Letwin A.4; no new regularity hypothesis on u. -/
theorem solution {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη
  have hE : Integrable (FunctionalInequalities.Analysis.energyDensity u η w)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply FunctionalInequalities.Analysis.integrable_energy hu hG hF.continuous hdet
      (FunctionalInequalities.Analysis.continuous_coord hη1) (FunctionalInequalities.Analysis.continuous_coord hw)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_right :
        HasCompactSupport (fun x => FunctionalInequalities.Analysis.coord η i x * FunctionalInequalities.Analysis.coord w j x)).mul_right
  exact FunctionalInequalities.Analysis.assemble_generator_readable hu hG hV hF hdet
    (fun i => FunctionalInequalities.Analysis.exists_lipschitz_compact_exp_gradient_test hu hη1 hηc hGw i)
    (fun i => FunctionalInequalities.Analysis.ae_fderiv_exp_gradient_test hu hη1 hGw i) hE
