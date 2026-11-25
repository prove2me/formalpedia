-- Prove2me | solution 1 for FrameHessian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:50:52.120157+00:00
-- url     : https://prove2.me/submissions/d5df0526-296f-406c-a09f-42e20befc1eb

module
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_FrameHessian
public import Theorems.Thm_GradientEuler
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} (hm : 1 ≤ m) {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m) (e v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)) (Real.cos t • e + Real.sin t • v)
        = (m : ℝ) * MvPolynomial.eval
            (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P
      ∧ inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)) (-Real.sin t • e + Real.cos t • v)
        = deriv (fun s : ℝ => MvPolynomial.eval
            (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)
          ![Real.cos t • e + Real.sin t • v, Real.cos t • e + Real.sin t • v]
        = (m : ℝ) * ((m : ℝ) - 1) * MvPolynomial.eval
            (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)
          ![Real.cos t • e + Real.sin t • v, -Real.sin t • e + Real.cos t • v]
        = ((m : ℝ) - 1) * deriv (fun s : ℝ => MvPolynomial.eval
            (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)
          ![-Real.sin t • e + Real.cos t • v, -Real.sin t • e + Real.cos t • v]
        = iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
            (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t
          + (m : ℝ) * MvPolynomial.eval
            (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P := by
  -- Abbreviations matching the `.tex`: `x = e_r = cos t • e + sin t • v`,
  -- `eθ = -sin t • e + cos t • v`.
  -- Step 1 (conjunct 1): the radial first derivative, from `GradientEuler`.
  have h1 : (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => y i) P) (Real.cos t • e + Real.sin t • v))
      (Real.cos t • e + Real.sin t • v) : ℝ)
      = (m : ℝ) * MvPolynomial.eval
          (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P :=
    (GradientEuler hm hhom (Real.cos t • e + Real.sin t • v)
      (Real.cos t • e + Real.sin t • v)).1
  -- Step 2 (conjunct 2): the tangential first derivative.
  -- the curve `γ s = cos s • e + sin s • v` is differentiable with `γ' s = eθ(s)`.
  have hcurve : HasDerivAt
      (fun r : ℝ => (Real.cos r • e + Real.sin r • v : EuclideanSpace ℝ (Fin n)))
      ((-Real.sin t) • e + Real.cos t • v) t :=
    ((Real.hasDerivAt_cos t).smul_const e).add ((Real.hasDerivAt_sin t).smul_const v)
  -- chain rule: `F = u ∘ γ` has derivative `∑ i, (pderiv i P)(x) * eθ i` at `t`.
  have hchain : HasDerivAt (fun r : ℝ => MvPolynomial.eval
        (fun i => (Real.cos r • e + Real.sin r • v : EuclideanSpace ℝ (Fin n)) i) P)
      (∑ i, MvPolynomial.eval
          (fun j => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) j)
          (pderiv i P) *
        ((-Real.sin t • e + Real.cos t • v : EuclideanSpace ℝ (Fin n)) i)) t := by
    have h := HasFDerivAt.comp_hasDerivAt t
      (MvPolyFDerivEuclidean P (Real.cos t • e + Real.sin t • v)) hcurve
    have hval : (∑ i, (MvPolynomial.eval
          (fun j => (Real.cos t • e + Real.sin t • v
            : EuclideanSpace ℝ (Fin n)) j) (pderiv i P)) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        ((-Real.sin t) • e + Real.cos t • v)
        = ∑ i, MvPolynomial.eval
            (fun j => (Real.cos t • e + Real.sin t • v
              : EuclideanSpace ℝ (Fin n)) j) (pderiv i P) *
          ((-Real.sin t • e + Real.cos t • v : EuclideanSpace ℝ (Fin n)) i) := by
      simp
    exact hval ▸ h
  have h2 : (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => y i) P) (Real.cos t • e + Real.sin t • v))
      (-Real.sin t • e + Real.cos t • v) : ℝ)
      = deriv (fun s : ℝ => MvPolynomial.eval
          (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t := by
    rw [(MvPolyGradientInner P (Real.cos t • e + Real.sin t • v)
      (-Real.sin t • e + Real.cos t • v)).1,
      hchain.deriv]
  -- Step 5 (conjunct 5): instantiate `GreatCircleSecondDeriv` at `C = 0`.
  have h5 := GreatCircleSecondDeriv P 0 e v t
  simp only [zero_add] at h5
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · -- conjunct 3
    rw [(GradientEuler hm hhom (Real.cos t • e + Real.sin t • v)
      (Real.cos t • e + Real.sin t • v)).2, h1]
    ring
  · -- conjunct 4
    rw [(GradientEuler hm hhom (Real.cos t • e + Real.sin t • v)
      (-Real.sin t • e + Real.cos t • v)).2, h2]
  · -- conjunct 5
    rw [h1] at h5
    linarith [h5]
