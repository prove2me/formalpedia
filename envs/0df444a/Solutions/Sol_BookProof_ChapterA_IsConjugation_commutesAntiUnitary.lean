-- Prove2me | solution 1 for BookProof.ChapterA.IsConjugation.commutesAntiUnitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:25.420984+00:00
-- url     : https://prove2.me/submissions/8c9355b6-d467-4502-948d-36ad6a62acbe

-- Generated from ChapterA1c.lean — solution of BookProof.ChapterA.IsConjugation.commutesAntiUnitary
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {θ : AntiUnitary V}
    (h : IsConjugation M θ) : CommutesAntiUnitary M θ := h.2
