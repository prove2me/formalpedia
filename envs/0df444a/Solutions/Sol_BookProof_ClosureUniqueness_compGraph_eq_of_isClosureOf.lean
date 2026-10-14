-- Prove2me | solution 1 for BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:46.944101+00:00
-- url     : https://prove2.me/submissions/d9a10bfe-76f6-4241-81f9-08e07e60b523

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_opGraph_eq_clGraph_of_isClosureOf
import Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_adjPairs_clGraph
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A) :
    compGraph A = factorGraph T := by

  have hgraph : opGraph A = clGraph T := opGraph_eq_clGraph_of_isClosureOf hA
  have hadj : adjPairs (opGraph A) = adjGraph T := by
    rw [hgraph, ← adjGraph_eq_adjPairs_clGraph]
  exact Set.ext fun p => exists_congr fun y =>
    and_congr (by rw [hgraph]) (by rw [hadj])
