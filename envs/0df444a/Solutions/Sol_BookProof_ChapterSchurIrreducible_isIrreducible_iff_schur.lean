-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:27:58.511783+00:00
-- url     : https://prove2.me/submissions/57add630-26f3-4921-93cc-f3b6991826f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_selfAdjoint_commutant_scalar
import Theorems.Thm_BookProof_ChapterA_System_schur_normal_irreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hM : M.IsNormal) :
    M.IsIrreducible ↔
      ∀ S : V →L[ℂ] V, M.Commutes S → IsSelfAdjoint S → ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by

  constructor
  · intro hirr S hS hsa
    obtain ⟨r, hr⟩ := selfAdjoint_commutant_scalar M hirr hsa hS
    exact ⟨(r : ℂ), hr⟩
  · intro hSchur
    exact System.schur_normal_irreducible M hM hSchur
