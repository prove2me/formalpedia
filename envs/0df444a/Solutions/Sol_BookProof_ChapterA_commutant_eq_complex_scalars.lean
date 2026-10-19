-- Prove2me | solution 1 for BookProof.ChapterA.commutant_eq_complex_scalars
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:49.717363+00:00
-- url     : https://prove2.me/submissions/6dda531a-20ca-4ace-b867-0bbfcfc4f286

-- Generated from ChapterA2b.lean — solution of BookProof.ChapterA.commutant_eq_complex_scalars
import Mathlib
import Definitions.Def_ChapterA2b
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hSchur : IsSchurFull M)
    (S : V →L[ℂ] V) :
    M.Commutes S ↔ ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by

  exact ⟨ fun h => hSchur S h, fun ⟨ c, hc ⟩ => by rw [ hc ] ; exact fun m hm => by simp  ⟩
