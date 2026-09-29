-- Prove2me | solution 1 for BookProof.ScalaronEdge.edge_normSq_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:42:15.304734+00:00
-- url     : https://prove2.me/submissions/d4e47635-36d5-4a29-b0ba-58baaa064400

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edge_normSq_hasDerivAt
import Mathlib
import Definitions.Def_ChapterScalaronEdge
open BookProof.ScalaronEdge










open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (fun t => ‖f t‖ ^ 2)
      (((starRingEnd ℂ) (deriv f x) * f x + (starRingEnd ℂ) (f x) * deriv f x).re) x := by

  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h1 : HasDerivAt f (deriv f x) x := (hfd x).hasDerivAt
  have hG : HasDerivAt (fun t => (starRingEnd ℂ) (f t) * f t)
      ((starRingEnd ℂ) (deriv f x) * f x + (starRingEnd ℂ) (f x) * deriv f x) x :=
    (h1.star).mul h1
  refine (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hG).congr_of_eventuallyEq ?_
  filter_upwards with t
  simp [Complex.sq_norm, Complex.normSq_apply]
