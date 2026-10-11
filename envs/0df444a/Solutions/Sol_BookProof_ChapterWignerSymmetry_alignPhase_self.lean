-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.alignPhase_self
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:23.717017+00:00
-- url     : https://prove2.me/submissions/bb44ea80-f903-4f67-bcbd-3aad92e91a01

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.alignPhase_self
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}
open BookProof.ChapterWignerSymmetry

theorem solution: alignPhase b T o o = 1 := by
  simp [alignPhase]
