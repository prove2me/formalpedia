-- Prove2me | solution 1 for BookProof.ChapterA3r.trace_permMat
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:24:53.366175+00:00
-- url     : https://prove2.me/submissions/b8e50fa1-503e-41cd-af69-2abac9354882

-- Generated from ChapterA3r.lean — theorem BookProof.ChapterA3r.trace_permMat
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3q
import Mathlib
import Definitions.Def_ChapterA3r
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.ChapterA3r


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q


theorem solution {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Matrix.trace (permMat σ) =
      ((Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card : ℂ) := by
  classical
  simp [Matrix.trace, permMat, Finset.sum_boole, eq_comm]

#print axioms solution
