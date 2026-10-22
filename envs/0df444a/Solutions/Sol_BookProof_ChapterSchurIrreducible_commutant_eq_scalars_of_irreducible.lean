-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:40:39.043493+00:00
-- url     : https://prove2.me/submissions/a89c7914-ecbf-4f6a-ba0d-4d70dba93cac

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_isSchurFull_of_irreducible
import Theorems.Thm_BookProof_ChapterA_commutant_eq_complex_scalars
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) (S : V →L[ℂ] V) :
    M.Commutes S ↔ ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := commutant_eq_complex_scalars M (isSchurFull_of_irreducible M hM hirr) S
