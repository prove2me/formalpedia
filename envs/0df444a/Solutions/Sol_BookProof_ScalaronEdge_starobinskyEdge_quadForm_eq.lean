-- Prove2me | solution 1 for BookProof.ScalaronEdge.starobinskyEdge_quadForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T13:56:32.273199+00:00
-- url     : https://prove2.me/submissions/39b16ad8-6a32-449c-b88f-8bb0018a6993

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.starobinskyEdge_quadForm_eq
import Mathlib
import Definitions.Def_ChapterScalaronEdge
import Theorems.Thm_BookProof_ScalaronEdge_starobinskyEdge_inner_eq
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
theorem solution (f : ccSchwartz ℝ) :
    quadForm (starobinskyEdgeHam M alpha) (ccEquiv ℝ f)
      = (∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2)
        + ∫ x, scalV M alpha x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by

  have hconj : (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))
      (starobinskyEdgeHam M alpha (ccEquiv ℝ f)) : ℂ)
      = (starRingEnd ℂ) (inner ℂ (starobinskyEdgeHam M alpha (ccEquiv ℝ f))
          ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))) :=
    (inner_conj_symm _ _).symm
  rw [quadForm, hconj, starobinskyEdge_inner_eq, Complex.conj_ofReal, Complex.ofReal_re]
