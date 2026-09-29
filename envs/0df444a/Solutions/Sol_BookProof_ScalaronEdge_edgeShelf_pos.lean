-- Prove2me | solution 1 for BookProof.ScalaronEdge.edgeShelf_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:42:14.342214+00:00
-- url     : https://prove2.me/submissions/75990053-49a6-4c39-b6e1-bc7796688be2

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edgeShelf_pos
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
theorem solution (hM : 0 < M) (halpha : 0 < alpha) : 0 < edgeShelf M alpha := by

  unfold edgeShelf; positivity
