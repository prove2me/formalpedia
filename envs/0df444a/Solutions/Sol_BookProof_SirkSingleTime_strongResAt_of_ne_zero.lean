-- Prove2me | solution 1 for BookProof.SirkSingleTime.strongResAt_of_ne_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T02:07:53.409083+00:00
-- url     : https://prove2.me/submissions/015d291a-4c4a-4f17-aff8-af77131cda2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.strongResAt_of_ne_zero
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_strongResAt_neg
import Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_pos_of_pos
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterStoneResolvent
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

set_option maxHeartbeats 1000000 in
theorem solution {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)
    (h : StrongResAt T S l) : StrongResAt T S m := by

  have hpos : ∀ l' : ℝ, 0 < l' → StrongResAt T S l' → StrongResAt T S m := by
    intro l' hl' h'
    rcases lt_or_gt_of_ne hm with hmneg | hmpos
    · have hmm : StrongResAt T S (-m) := strongResAt_of_pos_of_pos hl' (by linarith) h'
      have := strongResAt_neg (l := -m) (by linarith) hmm
      simpa using this
    · exact strongResAt_of_pos_of_pos hl' hmpos h'
  rcases lt_or_gt_of_ne hl with hlneg | hlpos
  · exact hpos (-l) (by linarith) (strongResAt_neg hl h)
  · exact hpos l hlpos h
