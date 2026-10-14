-- Prove2me | solution 1 for BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:39.128361+00:00
-- url     : https://prove2.me/submissions/455bcde0-b2b9-4a31-b859-c4d45391dacd

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clGraph_le_opGraph_of_isClosedExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F}
    (h : IsClosureOf T A) : opGraph A = clGraph T := le_antisymm h.2 (clGraph_le_opGraph_of_isClosedExtension h.1)
