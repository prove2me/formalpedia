-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:27:42.836291+00:00
-- url     : https://prove2.me/submissions/e83683a3-f30e-4cd6-a7db-ba6fd4e12552

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_commutant_scalar_of_irreducible
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
    (hirr : M.IsIrreducible) : IsSchurFull M := fun _ hS => commutant_scalar_of_irreducible M hM hirr hS
