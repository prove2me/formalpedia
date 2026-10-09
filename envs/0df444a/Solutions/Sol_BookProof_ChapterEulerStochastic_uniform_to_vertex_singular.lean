-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.uniform_to_vertex_singular
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:54:44.314806+00:00
-- url     : https://prove2.me/submissions/3a88123f-8a79-46e6-8701-3d2621447b71

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.uniform_to_vertex_singular
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : PreservesProb M) (hcollapse : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) :
    M.det = 0 := by

      rw [ Matrix.det_fin_two ];
      simp_all [ funext_iff, Fin.forall_fin_two, Matrix.mulVec ];
      have := hM ![1, 0] ; have := hM ![0, 1] ; norm_num [ IsProbVec ] at *;
      norm_num [ Matrix.vecHead, Matrix.vecTail, Matrix.mulVec ] at * ; nlinarith!
