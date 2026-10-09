-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.no_shift_invariant_unit_vector_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:37:29.895988+00:00
-- url     : https://prove2.me/submissions/912270d9-047a-4dc7-806f-ebeb2ec83c8c

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.no_shift_invariant_unit_vector'
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_eq_self_iff
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ f : L2Z, ‖f‖ = 1 ∧ ∀ m : ℤ, shiftOp m f = f := by

  rintro ⟨f, hnorm, hinv⟩
  have h0 : f = 0 := shiftOp_eq_self_iff (m := 1) one_ne_zero (hinv 1)
  rw [h0, norm_zero] at hnorm
  exact one_ne_zero hnorm.symm
