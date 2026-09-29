-- Prove2me | solution 1 for FastFourierTransform.fftAddCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:26:22.638735+00:00
-- url     : https://prove2.me/submissions/98309df1-b7d6-459a-9632-b57210ec26c6

import Mathlib
import Definitions.Def_FastFourierTransform_opCount

open FastFourierTransform

theorem solution (p : ℕ) : fftAddCount p = p * 2 ^ p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [fftAddCount, ih]; ring
