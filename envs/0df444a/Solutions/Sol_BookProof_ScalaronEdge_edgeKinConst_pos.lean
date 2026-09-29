-- Prove2me | solution 1 for BookProof.ScalaronEdge.edgeKinConst_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:42:12.577346+00:00
-- url     : https://prove2.me/submissions/b0ee2cd0-df12-4131-a324-37c351b55fe2

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edgeKinConst_pos
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
theorem solution {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < edgeKinConst A B := by

  unfold edgeKinConst
  have : 0 < A + B := by linarith
  positivity
