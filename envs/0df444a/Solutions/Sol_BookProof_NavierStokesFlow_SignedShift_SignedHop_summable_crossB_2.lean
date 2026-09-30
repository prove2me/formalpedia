-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossB
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:57:55.132309+00:00
-- url     : https://prove2.me/submissions/69d64d12-c3fb-4e3e-9ee8-5dcb6da5dfd7

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossB
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_norm_crossB_le
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_maj_shift
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

set_option maxHeartbeats 1000000 in
theorem solution {X Y : ι → ℂ}
    (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) :
    Summable (S.crossB X Y) := by

  refine Summable.of_norm (Summable.of_nonneg_of_le (fun β => norm_nonneg _) (fun β => ?_)
    (((ShiftData.summable_comp_shift S.maj hX).add hY).mul_left (1 / 2)))
  have h := norm_crossB_le S X Y β
  simp only [maj_shift]
  nlinarith [sq_nonneg (S.maj.ampSeq X (S.shift β) - ‖Y β‖),
    ShiftData.ampSeq_nonneg S.maj X (S.shift β), norm_nonneg (Y β), h]
