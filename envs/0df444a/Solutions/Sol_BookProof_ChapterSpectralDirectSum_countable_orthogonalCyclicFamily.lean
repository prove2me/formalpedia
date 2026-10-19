-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:11.709198+00:00
-- url     : https://prove2.me/submissions/d5e22f23-66ee-43e4-ac05-7cc765520fd1

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_one_lt_dist_of_orthogonalCyclicFamily
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterSpectralDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

set_option maxHeartbeats 1000000 in
theorem solution [TopologicalSpace.SeparableSpace H] {S : Set H}
    (hS : OrthogonalCyclicFamily T hT S) : S.Countable := by

  refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun x : H => Metric.ball x (1 / 2)) ?_
    (fun x _ => Metric.isOpen_ball) (fun x _ => ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have := one_lt_dist_of_orthogonalCyclicFamily T hT hS hx hy hxy
  linarith
