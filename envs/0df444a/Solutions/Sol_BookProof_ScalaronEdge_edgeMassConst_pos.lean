-- Prove2me | solution 1 for BookProof.ScalaronEdge.edgeMassConst_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:42:13.487234+00:00
-- url     : https://prove2.me/submissions/55e8d794-de34-49d7-88b3-0c77efd7cf25

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edgeMassConst_pos
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
theorem solution {c : ℝ} (hc : 0 < c) : 0 < edgeMassConst c := by

  unfold edgeMassConst; linarith
