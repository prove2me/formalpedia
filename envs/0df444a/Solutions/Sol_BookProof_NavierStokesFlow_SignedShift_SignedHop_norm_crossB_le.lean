-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossB_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:38:24.955665+00:00
-- url     : https://prove2.me/submissions/c4deccaf-7b59-409c-85a6-0a895fe8de25

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.SignedHop.norm_crossB_le
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
    ‖S.crossB X Y β‖ ≤ S.maj.ampSeq X (S.shift β) * ‖Y β‖ := by

  simp only [crossB, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
  have h1 : |S.amp β| * ‖X (S.shift β)‖ ≤ S.bnd (S.shift β) * ‖X (S.shift β)‖ :=
    mul_le_mul_of_nonneg_right (le_trans (S.abs_amp_le_bnd β) (S.bnd_mono β)) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
