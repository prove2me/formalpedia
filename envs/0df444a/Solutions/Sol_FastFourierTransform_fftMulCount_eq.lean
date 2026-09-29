-- Prove2me | solution 1 for FastFourierTransform.fftMulCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:26:22.625062+00:00
-- url     : https://prove2.me/submissions/0da5b299-37b2-4951-92ea-fb4de8e805dd

import Mathlib
import Definitions.Def_FastFourierTransform_opCount

open FastFourierTransform

theorem solution (p : ℕ) : 2 * fftMulCount p = p * 2 ^ p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [fftMulCount, mul_add, ← mul_assoc, mul_comm 2 2, mul_assoc, ih]; ring
