-- Prove2me | solution 1 for BianchiIX.fderiv_variable_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:56:03.279941+00:00
-- url     : https://prove2.me/submissions/bec17921-6501-4bab-a8ee-0f7fb663f1b3

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E}
    {A : E →L[ℝ] ℝ} {b : ℝ} (hF : DifferentiableAt ℝ F (x, τ x))
    (hτ : DifferentiableAt ℝ τ x) (hleft : HasFDerivAt (fun y => F (y, τ x)) A x)
    (hright : HasDerivAt (fun t => F (x, t)) b (τ x)) (v : E) :
    fderiv ℝ (fun y => F (y, τ y)) x v = A v + b * fderiv ℝ τ x v := by
  let J := fderiv ℝ F (x, τ x)
  have h0 : J (v, 0) = A v := congrArg (fun B : E →L[ℝ] ℝ => B v)
    ((hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (τ x))).unique hleft)
  have h1 : J (0, 1) = b :=
    (hF.hasFDerivAt.comp_hasDerivAt (τ x)
      ((hasDerivAt_const (τ x) x).prodMk (hasDerivAt_id (τ x)))).unique hright
  have H := hF.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hτ.hasFDerivAt)
  change HasFDerivAt (fun y => F (y, τ y)) _ _ at H
  rw [H.fderiv]
  change J (v, fderiv ℝ τ x v) = _
  have heq : (v, fderiv ℝ τ x v) = (v, (0 : ℝ)) + (fderiv ℝ τ x v) • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  rw [heq, map_add, map_smul, smul_eq_mul, h0, h1]
  ring
