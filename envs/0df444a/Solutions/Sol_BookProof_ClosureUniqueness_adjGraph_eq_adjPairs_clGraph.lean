-- Prove2me | solution 1 for BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:44.599629+00:00
-- url     : https://prove2.me/submissions/8fa0146c-3260-413e-940b-189891699a0e

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (T : D →ₗ[ℂ] F) : adjGraph T = adjPairs (clGraph T) := by

  refine le_antisymm ?_ ?_
  · intro p hp q hq
    have hclosed : IsClosed {r : F × F | (inner ℂ r.2 p.1 : ℂ) = inner ℂ r.1 p.2} :=
      isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
    exact clGraph_subset_of_isClosed hclosed
      (fun v => hp _ (mem_opGraph T v)) hq
  · intro p hp q hq
    exact hp q (opGraph_le_clGraph T hq)
