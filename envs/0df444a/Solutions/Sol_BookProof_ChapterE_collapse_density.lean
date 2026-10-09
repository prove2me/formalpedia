-- Prove2me | solution 1 for BookProof.ChapterE.collapse_density
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:27:19.639527+00:00
-- url     : https://prove2.me/submissions/af74a056-661b-4344-999f-19cf8e305940

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.collapse_density
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    (!![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)
      = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + (1 / 2 * Real.cos (2 * t)) • !![1, 0; 0, -1] := by

  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring
