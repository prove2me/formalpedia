-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.genOp_bAvg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:17:05.568633+00:00
-- url     : https://prove2.me/submissions/a1d7021d-aee9-4d58-85a3-2fae0dd5fb35

import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.genOp_bAvg
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)


theorem solution (x : H) (a : ℝ) :
    G.genOp ⟨G.bAvg x a, G.bAvg_mem_genDomain x a⟩ = Complex.I • (G.U a x - x) := by
  refine G.genOp_eq_of_hasDerivAt ?_
  have h : (fun s : ℝ => G.U s (G.bAvg x a))
      = fun s : ℝ => G.bAvg x (s + a) - G.bAvg x s := by
    funext s; exact G.apply_bAvg s a x
  rw [h]
  have hfa : HasDerivAt (fun u : ℝ => G.bAvg x u) (G.U a x) (0 + a) := by
    simpa using G.hasDerivAt_bAvg x a
  have h1 : HasDerivAt (fun s : ℝ => G.bAvg x (s + a)) (G.U a x) 0 :=
    HasDerivAt.comp_add_const 0 a hfa
  have h2 : HasDerivAt (fun s : ℝ => G.bAvg x s) (G.U 0 x) 0 := G.hasDerivAt_bAvg x 0
  have h3 := h1.sub h2
  rw [G.map_zero] at h3
  convert h3 using 1
  · rfl
  · rw [smul_smul]; simp

