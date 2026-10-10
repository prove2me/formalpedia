-- Prove2me | solution 1 for BookProof.ChapterH8.adjoint_aeval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:52:33.784295+00:00
-- url     : https://prove2.me/submissions/aec90315-12ce-4d9b-a6d3-7af7ac57000c

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.adjoint_aeval
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
open BookProof.ChapterH8



open ContinuousLinearMap

noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F) (p : Polynomial ℂ) :
    adjoint (Polynomial.aeval A p) = Polynomial.aeval (adjoint A) (p.map (starRingEnd ℂ)) := by

  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, hp, hq]
  | monomial k c =>
      simp [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, ← star_eq_adjoint,
        star_pow, Polynomial.map_monomial]
