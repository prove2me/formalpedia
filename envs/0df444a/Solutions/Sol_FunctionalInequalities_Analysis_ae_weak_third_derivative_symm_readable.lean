-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:47.471169+00:00
-- url     : https://prove2.me/submissions/716b63d7-07c7-4b0c-8ca0-966811ec32aa

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Weak derivatives are unique almost everywhere. -/
theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e
end
universe u
end
end

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
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.HasWeakDerivAlong.congr_left {f f' g : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v) (hff' : f =ᵐ[(volume : Measure E)] f') :
    HasWeakDerivAlong f' g v := by
  refine ⟨h.1.congr hff', h.2.1, ?_⟩
  intro ψ hψ hψc
  have hp :
      (fun x => f' x * fderiv ℝ ψ x v) =ᵐ[(volume : Measure E)]
        (fun x => f x * fderiv ℝ ψ x v) := by
    filter_upwards [hff'] with x hx
    rw [hx]
  rw [integral_congr_ae hp]
  exact h.2.2 ψ hψ hψc
private lemma FunctionalInequalities.Analysis.HasWeakDerivAlong.congr_right {f g g' : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v) (hgg' : g =ᵐ[(volume : Measure E)] g') :
    HasWeakDerivAlong f g' v := by
  refine ⟨h.1, h.2.1.congr hgg', ?_⟩
  intro ψ hψ hψc
  have hi := h.2.2 ψ hψ hψc
  have hp :
      (fun x => g x * ψ x) =ᵐ[(volume : Measure E)]
        (fun x => g' x * ψ x) := by
    filter_upwards [hgg'] with x hx
    rw [hx]
  rw [integral_congr_ae hp] at hi
  exact hi
end FiniteDimensional
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
private lemma FunctionalInequalities.Analysis.fderiv_apply_apply_symm [CompleteSpace E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hφ2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfd' : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ2.fderiv_right (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hfd'.differentiable (by simp)).differentiableAt
  have hcv :
      DifferentiableAt ℝ (fun _ : E => v) x :=
    (differentiable_const v : Differentiable ℝ (fun _ : E => v)).differentiableAt
  have hcw :
      DifferentiableAt ℝ (fun _ : E => w) x :=
    (differentiable_const w : Differentiable ℝ (fun _ : E => w)).differentiableAt
  have hv := fderiv_clm_apply hfd hcv
  have hw := fderiv_clm_apply hfd hcw
  have hv' := congrArg (fun L : E →L[ℝ] ℝ => L w) hv
  have hw' := congrArg (fun L : E →L[ℝ] ℝ => L v) hw
  simp at hv' hw'
  have hs :=
    second_derivative_symmetric
      (fun y => (hφ2.differentiable (by norm_num) y).hasFDerivAt)
      hfd.hasFDerivAt w v
  calc
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
        ((fderiv ℝ (fderiv ℝ φ) x) w) v := hv'
    _ = ((fderiv ℝ (fderiv ℝ φ) x) v) w := hs
    _ = fderiv ℝ (fun y => fderiv ℝ φ y w) x v := hw'.symm
end InnerProduct
private lemma FunctionalInequalities.Analysis.contDiff_fderiv_apply [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) := by
  have hφ2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfd : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ2.fderiv_right (by norm_num)
  exact hfd.clm_apply
    (contDiff_const : ContDiff ℝ 1 (fun _ : E => v))
end StructuredSpace
/-- **Symmetry of the weak third derivative** (weak Letwin route): for `u ∈ C¹` with Lipschitz gradient, if
`T · k i j` is the weak derivative of the Hessian entry `Hᵢⱼ` along `eₖ` for all indices, then a.e. `Tₖᵢⱼ = Tᵢₖⱼ` and
`Tₖᵢⱼ = Tₖⱼᵢ`. -/
theorem solution {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ k i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by
  let e : Fin n → EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ

  have hcoord (i j : Fin n) :
      (fun x => fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) := by
    filter_upwards [hG.ae_differentiableAt] with x hx
    exact FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff hx

  have hHsym (i j : Fin n) :
      (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x j i) := by
    filter_upwards [hG.ae_differentiableAt] with x hx
    exact FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff hu hx

  have hgi (j : Fin n) :
      LipschitzWith (‖(innerSL ℝ) (e j)‖₊ * G)
        (fun x => fderiv ℝ u x (e j)) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e j)).lipschitz.comp hG)

  have hweak (i j : Fin n) :
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => fderiv ℝ u x (e j))
        (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (e i) := by
    exact FunctionalInequalities.Analysis.HasWeakDerivAlong.congr_right
      (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable (hgi j) (e i)) (hcoord i j)

  have hfirst (k i j : Fin n) :
      (fun x => T x k i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => T x k j i) := by
    have h' := FunctionalInequalities.Analysis.HasWeakDerivAlong.congr_left (hT k j i) (hHsym j i)
    exact (hT k i j).ae_eq h'

  have hcomm (k i j : Fin n) :
      (fun x => T x k i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => T x i k j) := by
    apply ae_eq_of_integral_contDiff_smul_eq (hT k i j).2.1 (hT i k j).2.1
    intro φ hφ hφc
    have hφ1 : ContDiff ℝ 1 φ :=
      hφ.of_le (WithTop.coe_le_coe.mpr le_top)
    have hφk : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (e k)) :=
      FunctionalInequalities.Analysis.contDiff_fderiv_apply hφ (e k)
    have hφi : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (e i)) :=
      FunctionalInequalities.Analysis.contDiff_fderiv_apply hφ (e i)
    have hφkc : HasCompactSupport (fun x => fderiv ℝ φ x (e k)) :=
      hφc.fderiv_apply ℝ (e k)
    have hφic : HasCompactSupport (fun x => fderiv ℝ φ x (e i)) :=
      hφc.fderiv_apply ℝ (e i)
    have e₁ := (hweak i j).2.2
      (fun x => fderiv ℝ φ x (e k)) hφk hφkc
    have e₂ := (hT k i j).2.2 φ hφ1 hφc
    have e₃ := (hweak k j).2.2
      (fun x => fderiv ℝ φ x (e i)) hφi hφic
    have e₄ := (hT i k j).2.2 φ hφ1 hφc
    have hleft :
        (∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            -(∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j *
              fderiv ℝ φ x (e k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
                linarith [e₂]
        _ = ∫ x, fderiv ℝ u x (e j) *
              fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
                linarith [e₁]
    have hright :
        (∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            -(∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x k j *
              fderiv ℝ φ x (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
                linarith [e₄]
        _ = ∫ x, fderiv ℝ u x (e j) *
              fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
                linarith [e₃]
    have hsecond :
        (fun x => fderiv ℝ u x (e j) *
          fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)) =
          (fun x => fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)) := by
      funext x
      rw [FunctionalInequalities.Analysis.fderiv_apply_apply_symm hφ x (e k) (e i)]
    have hmul :
        (∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            ∫ x, fderiv ℝ u x (e j) *
              fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hleft
        _ = ∫ x, fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
            rw [hsecond]
        _ = ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
          hright.symm
    simpa only [smul_eq_mul, mul_comm] using hmul

  apply ae_all_iff.2
  intro k
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro j
  filter_upwards [hcomm k i j, hfirst k i j] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩
