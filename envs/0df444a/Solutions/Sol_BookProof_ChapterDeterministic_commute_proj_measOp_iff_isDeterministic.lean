-- Prove2me | solution 1 for BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:23.554906+00:00
-- url     : https://prove2.me/submissions/0c16ae13-1f19-4401-bffd-b96c4928d1dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterDeterministic.lean — solution of BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterDeterministic
import Theorems.Thm_BookProof_ChapterDeterministic_commute_proj_measOp_iff_isDeterministicCol
open BookProof.ChapterDeterministic



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ a b : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministic U := by

  constructor;
  · exact fun h => fun b => ( commute_proj_measOp_iff_isDeterministicCol U b ).mp fun a => h a b;
  · intro h a b; specialize h b; exact (commute_proj_measOp_iff_isDeterministicCol U b).mpr h a;
