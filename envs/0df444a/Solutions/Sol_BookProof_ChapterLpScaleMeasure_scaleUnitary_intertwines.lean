-- Prove2me | solution 1 for BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:26:55.847576+00:00
-- url     : https://prove2.me/submissions/fb31c006-9be5-4aa6-a5a7-b0c40c9a3507

-- Generated from ChapterLpScaleMeasure.lean — solution of BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
import Theorems.Thm_BookProof_ChapterLpScaleMeasure_scaleUnitary_coeFn
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure



noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

set_option maxHeartbeats 1000000 in
theorem solution (hc0 : c ≠ 0) (hctop : c ≠ ⊤) {g : α → ℂ}
    (hg : MemLp g ⊤ (c • nu)) (u : Lp ℂ 2 (c • nu)) :
    (scaleUnitary hc0 hctop (multOp g hg u) : α → ℂ)
      =ᵐ[nu] fun x => g x * (scaleUnitary (nu := nu) hc0 hctop u : α → ℂ) x := by

  have h2 : (↑↑(multOp g hg u) : α → ℂ) =ᵐ[nu] fun x => g x * (u : α → ℂ) x := by
    have h := multOp_coeFn (μ := c • nu) g hg u
    rwa [Filter.EventuallyEq, ae_smul_measure_eq hc0] at h
  filter_upwards [scaleUnitary_coeFn hc0 hctop (multOp g hg u), h2,
    scaleUnitary_coeFn hc0 hctop u] with x h1 h2 h3
  rw [h1, h2, h3]
  ring
