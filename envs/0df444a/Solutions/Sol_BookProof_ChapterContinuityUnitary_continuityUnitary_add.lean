-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.continuityUnitary_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:07:06.372991+00:00
-- url     : https://prove2.me/submissions/3d37e148-f725-410c-9ecd-f6b3fba78b4f

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]

open scoped BigOperators Matrix TensorProduct

theorem solution (v : ZMod N → ℝ) (s t : ℝ) :
    continuityUnitary v (s + t) = continuityUnitary v s * continuityUnitary v t := by
  unfold continuityUnitary
  set A : Matrix (ZMod N) (ZMod N) ℂ := ((s : ℂ) * Complex.I) • continuityHamiltonian v
  set B : Matrix (ZMod N) (ZMod N) ℂ := ((t : ℂ) * Complex.I) • continuityHamiltonian v
  have hcomm : Commute A B :=
    ((Commute.refl (continuityHamiltonian v)).smul_left ((s : ℂ) * Complex.I)).smul_right
      ((t : ℂ) * Complex.I)
  have hsum : (((s + t : ℝ) : ℂ) * Complex.I) • continuityHamiltonian v = A + B := by
    simp [A, B, Complex.ofReal_add, add_mul, add_smul]
  rw [hsum]
  exact Matrix.exp_add_of_commute A B hcomm
