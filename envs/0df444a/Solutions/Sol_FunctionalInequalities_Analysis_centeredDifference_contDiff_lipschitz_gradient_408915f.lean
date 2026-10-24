-- Prove2me | solution 1 for FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:05:07.116843+00:00
-- url     : https://prove2.me/submissions/9ecfe882-1142-4f28-8e72-0a3c14faf24e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open scoped RealInnerProductSpace
section CenteredDifference
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.increment_fderiv {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) =
      fun y => fderiv ℝ u (y + h) + fderiv ℝ u (y - h) -
        (fderiv ℝ u y + fderiv ℝ u y) := by
  funext y
  have hp : DifferentiableAt ℝ (fun z => u (z + h)) y :=
    (hu (y + h)).comp y (differentiableAt_id.add_const h)
  have hm : DifferentiableAt ℝ (fun z => u (z - h)) y :=
    (hu (y - h)).comp y (differentiableAt_id.sub_const h)
  simp only [two_mul]
  rw [fderiv_fun_sub (hp.fun_add hm) ((hu y).fun_add (hu y)),
    fderiv_fun_add hp hm, fderiv_fun_add (hu y) (hu y),
    fderiv_comp_add_right]
  simpa only [sub_eq_add_neg] using
    congrArg
      (fun q => fderiv ℝ u (y + h) + q - (fderiv ℝ u y + fderiv ℝ u y))
      (fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := y) (-h))
private lemma FunctionalInequalities.Analysis.increment_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x =
      gradient u (x + h) + gradient u (x - h) - 2 • gradient u x := by
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) x) = _
  rw [increment_fderiv hu h]
  simp only [map_sub, map_add, gradient, two_smul]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Consumer adapter for the centered second difference used in the weak
Letwin Hessian increment estimate. C1 and the gradient Lipschitz bound suffice. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) ∧
      LipschitzWith (4 * G)
        (gradient (fun x => u (x + h) + u (x - h) - 2 * u x)) := by
  have hdu : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hcp : ContDiff ℝ 1
      (fun x : EuclideanSpace ℝ (Fin n) => x + h) :=
    contDiff_id.add contDiff_const
  have hcm : ContDiff ℝ 1
      (fun x : EuclideanSpace ℝ (Fin n) => x - h) :=
    contDiff_id.sub contDiff_const
  have hp : ContDiff ℝ 1 (fun x => u (x + h)) := by
    simpa only [Function.comp_def] using hu.comp hcp
  have hm : ContDiff ℝ 1 (fun x => u (x - h)) := by
    simpa only [Function.comp_def] using hu.comp hcm
  have htwo : ContDiff ℝ 1 (fun x => 2 * u x) := by
    simpa only [two_mul] using hu.add hu
  have hC1 :
      ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) :=
    (hp.add hm).sub htwo
  have htp : LipschitzWith (1 : NNReal)
      (fun x : EuclideanSpace ℝ (Fin n) => x + h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_add_right, le_refl]
  have htm : LipschitzWith (1 : NNReal)
      (fun x : EuclideanSpace ℝ (Fin n) => x - h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_sub_right, le_refl]
  have hGp : LipschitzWith G (fun x => gradient u (x + h)) := by
    simpa only [Function.comp_def, mul_one] using hG.comp htp
  have hGm : LipschitzWith G (fun x => gradient u (x - h)) := by
    simpa only [Function.comp_def, mul_one] using hG.comp htm
  have hG2 : LipschitzWith (2 * G)
      (fun x => (2 : ℕ) • gradient u x) := by
    simpa only [two_mul, two_smul] using hG.add hG
  have hgrad : LipschitzWith (G + G + 2 * G)
      (fun x => gradient u (x + h) + gradient u (x - h) -
        (2 : ℕ) • gradient u x) :=
    (hGp.add hGm).sub hG2
  have hfun :
      (fun x => gradient u (x + h) + gradient u (x - h) -
        (2 : ℕ) • gradient u x) =
      gradient (fun x => u (x + h) + u (x - h) - 2 * u x) := by
    funext x
    exact (increment_gradient hdu h x).symm
  have hconst : G + G + 2 * G = 4 * G := by
    ring
  rw [hconst, hfun] at hgrad
  exact ⟨hC1, hgrad⟩
