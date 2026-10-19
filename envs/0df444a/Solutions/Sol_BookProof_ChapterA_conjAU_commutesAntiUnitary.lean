-- Prove2me | solution 1 for BookProof.ChapterA.conjAU_commutesAntiUnitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:07.906751+00:00
-- url     : https://prove2.me/submissions/5087230d-f763-45fe-bd86-cab74f83eea0

-- Generated from ChapterA2d.lean — solution of BookProof.ChapterA.conjAU_commutesAntiUnitary
import Mathlib
import Definitions.Def_ChapterA2d
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {N : System ℂ W} {α : V ≃ₗᵢ[ℂ] W}
    (hα : IsSystemIso M N α) {θ : AntiUnitary V} (hθ : CommutesAntiUnitary M θ) :
    CommutesAntiUnitary N (conjAU α θ) := by

  intro n hn; simp_all [ IsSystemIso, CommutesAntiUnitary ] ;
  obtain ⟨ m, hm, rfl ⟩ := hn; simp [ conjCLM_apply, hθ m hm ] ;
