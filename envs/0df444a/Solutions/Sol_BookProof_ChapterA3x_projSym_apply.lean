-- Prove2me | solution 1 for BookProof.ChapterA3x.projSym_apply
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:17:36.3574+00:00
-- url     : https://prove2.me/submissions/c64f80ac-f0e6-4072-83a3-3d3c133cdb3c

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projSym_apply
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem solution {N : ℕ} (a b : Idx N) :
    projSym N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
      (if b = a ∘ σ then (1 : ℂ) else 0) := by
  simp [BookProof.ChapterA3n.projSym, permMat, Matrix.sum_apply]

#print axioms solution
