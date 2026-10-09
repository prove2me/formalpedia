-- Prove2me | solution 1 for BookProof.ChapterF3.overlap_prod_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:00:26.71995+00:00
-- url     : https://prove2.me/submissions/77ba0378-973e-4c4e-a801-b5472e124e52

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.overlap_prod_pos
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    0 < ∏ i ∈ s, Real.sqrt (w i / (2 * Real.pi)) := by

  exact Finset.prod_pos fun i hi => Real.sqrt_pos.mpr ( div_pos ( hw i hi ) ( by positivity ) )
