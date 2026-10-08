-- Prove2me | solution 1 for BookProof.ChapterA3r.trace_projSym_two
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:24:42.4615+00:00
-- url     : https://prove2.me/submissions/87da6424-c8db-4e27-b48b-d57c55526d87

-- Generated from ChapterA3r.lean — theorem BookProof.ChapterA3r.trace_projSym_two
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3q
import Mathlib
import Definitions.Def_ChapterA3r
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3r


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q


set_option maxRecDepth 4096 in
theorem solution : Matrix.trace (projSym 2) = 10 := by
  classical
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hs (f : Idx 2 → ℂ) :
      ∑ a, f a = ∑ x : Fin 4, ∑ y : Fin 4, f ![x, y] := by
    rw [← (finTwoArrowEquiv (Fin 4)).symm.sum_comp]
    simp [Fintype.sum_prod_type, finTwoArrowEquiv]
  simp only [Matrix.trace]
  rw [hs]
  simp only [BookProof.ChapterA3n.projSym, Matrix.smul_apply, hp,
    Finset.sum_pair hn, Matrix.add_apply, permMat, Matrix.of_apply]
  norm_num [Fin.sum_univ_succ, Function.comp_def, funext_iff,
    Equiv.swap_apply_def]
  norm_num [Fin.ext_iff]

#print axioms solution
