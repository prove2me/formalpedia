-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:57:58.306978+00:00
-- url     : https://prove2.me/submissions/f6fc483b-8865-4001-80ff-df1d324316f8

-- Generated from ChapterFreeFieldBornFiberTwo.lean — solution of BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hn : 0 < n) :
    ¬ Function.Injective (bornMapSphere n) := by

  unfold bornMapSphere; intro h; simp_all only [Function.Injective, Subtype.mk.injEq,
      Subtype.forall, mem_sphere_iff_norm, sub_zero]
  contrapose! h
  refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, ?_, -EuclideanSpace.single ⟨0, hn⟩ 1, ?_, ?_, ?_⟩ <;>
    norm_num [EuclideanSpace.norm_eq]
  · ext; simp [bornMap]
  · exact ne_of_apply_ne (fun x => x ⟨0, hn⟩) (by norm_num)
