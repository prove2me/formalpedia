-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossA
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:48:30.679557+00:00
-- url     : https://prove2.me/submissions/c1129b2a-837c-41bd-b839-2accdc630cf3

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.summable_crossA
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_norm_crossA_le
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
    Summable (S.crossA X Y) := by

  refine Summable.of_norm (Summable.of_nonneg_of_le (fun β => norm_nonneg _) (fun β => ?_)
    ((hX.add (ShiftData.summable_comp_shift S.maj hY)).mul_left (1 / 2)))
  have h := norm_crossA_le S X Y β
  simp only [maj_shift]
  nlinarith [sq_nonneg (S.maj.ampSeq X β - ‖Y (S.shift β)‖),
    ShiftData.ampSeq_nonneg S.maj X β, norm_nonneg (Y (S.shift β)), h]
