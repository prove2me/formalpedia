-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossA_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:36:53.900103+00:00
-- url     : https://prove2.me/submissions/c1d9f55f-ec09-4206-9346-c8eb17fe847a

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossA_le
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

set_option maxHeartbeats 1000000 in
theorem solution (X Y : ι → ℂ) (β : ι) :
    ‖S.crossA X Y β‖ ≤ S.maj.ampSeq X β * ‖Y (S.shift β)‖ := by

  simp only [crossA, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
  have h : |S.amp β| * ‖X β‖ ≤ S.bnd β * ‖X β‖ :=
    mul_le_mul_of_nonneg_right (S.abs_amp_le_bnd β) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
