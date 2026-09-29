-- Prove2me | solution 1 for BookProof.ScalaronEdge.scalV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:16:49.585643+00:00
-- url     : https://prove2.me/submissions/5db72bae-07af-45a3-b283-0a6cf0523bcc

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.scalV_nonneg
import Mathlib
import Definitions.Def_ChapterScalaronEdge
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
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
/-- `scalV M alpha` is by definition `fun phi => starobinskyV M alpha phi`, so
non-negativity is exactly `BookProof.Starobinsky.starobinskyV_nonneg`. -/
theorem solution (halpha : 0 < alpha) (x : ℝ) : 0 ≤ scalV M alpha x := by
  have h : (0 : ℝ) ≤ starobinskyV M alpha x :=
    BookProof.Starobinsky.starobinskyV_nonneg halpha x
  first
    | exact h
    | (unfold scalV; exact h)
    | simpa [scalV] using h
    | simpa [scalV, starobinskyV] using h
