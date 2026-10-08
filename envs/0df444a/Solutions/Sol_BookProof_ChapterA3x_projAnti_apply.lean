-- Prove2me | solution 1 for BookProof.ChapterA3x.projAnti_apply
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:17:37.728934+00:00
-- url     : https://prove2.me/submissions/73751634-3a32-4bde-af7c-6a10adc15979

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projAnti_apply
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem solution {N : ℕ} (a b : Idx N) :
    projAnti N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
      signC σ * (if b = a ∘ σ then (1 : ℂ) else 0) := by
  simp [projAnti, permMat, Matrix.sum_apply, signC]

#print axioms solution
