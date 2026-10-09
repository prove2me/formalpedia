-- Prove2me | solution 1 for BookProof.ChapterG2.not_isProbabilityMeasure_cond_null
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:20:47.700326+00:00
-- url     : https://prove2.me/submissions/1954a1ab-727d-4002-bab8-e50480f317e7

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.not_isProbabilityMeasure_cond_null
import Mathlib
import Definitions.Def_ChapterG2
import Theorems.Thm_BookProof_ChapterG2_cond_of_null
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure Ω) {C : Set Ω}
    (hC : μ C = 0) : ¬ IsProbabilityMeasure μ[|C] := by

  intro h;
  have := congr_arg ( fun m => m Set.univ ) ( cond_of_null μ hC ) ;    simp_all [
      IsProbabilityMeasure.measure_univ ] ;
