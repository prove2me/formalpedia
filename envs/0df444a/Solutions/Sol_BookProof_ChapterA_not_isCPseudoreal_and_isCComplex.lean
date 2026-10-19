-- Prove2me | solution 1 for BookProof.ChapterA.not_isCPseudoreal_and_isCComplex
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:32.473385+00:00
-- url     : https://prove2.me/submissions/3847e321-416e-4ee8-922c-f4730e2ab187

-- Generated from ChapterA1c.lean — solution of BookProof.ChapterA.not_isCPseudoreal_and_isCComplex
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) :
    ¬ (IsCPseudoreal M ∧ IsCComplex M) := fun h => h.2 h.1.2
