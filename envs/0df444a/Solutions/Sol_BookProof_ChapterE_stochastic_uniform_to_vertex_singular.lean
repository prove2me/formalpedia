-- Prove2me | solution 1 for BookProof.ChapterE.stochastic_uniform_to_vertex_singular
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:27:32.394736+00:00
-- url     : https://prove2.me/submissions/ca6f0c6a-2e70-4e3f-82d7-b1fd595c43b0

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.stochastic_uniform_to_vertex_singular
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hcol : ∀ j, ∑ i, M i j = 1)
    (huniform : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) :
    M.det = 0 := by

  simp_all [ funext_iff, Fin.forall_fin_two, Matrix.det_fin_two ];
  norm_num [ Matrix.mulVec ] at huniform ; nlinarith!
