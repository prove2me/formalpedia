-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.X_mul_coordCombo_even
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:47.836794+00:00
-- url     : https://prove2.me/submissions/4bffeccf-2bbb-4b95-9b7c-c2e685d79f5b

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.X_mul_coordCombo_even
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : ℕ → ℝ) (M : ℕ) (ha : a (M + 1) = 0) :
    X i * coordCombo i a 0 M = coordCombo i (fun k => a k + 2 * (k + 1) * a (k + 1)) 1 M := by

  have hL : X i * coordCombo i a 0 M
      = (∑ m ∈ Finset.range (M + 1), ((a m : ℝ) : ℂ) • hermiteFactor i (2 * m + 1))
        + ∑ m ∈ Finset.range (M + 1),
            ((a m : ℝ) : ℂ) • (((2 * m : ℕ) : ℂ) • hermiteFactor i (2 * m - 1)) := by
    rw [coordCombo, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, hermiteFactor_X_mul, smul_add]
    push_cast
    ring_nf
  have hsecond : (∑ m ∈ Finset.range (M + 1),
      ((a m : ℝ) : ℂ) • (((2 * m : ℕ) : ℂ) • hermiteFactor i (2 * m - 1)))
      = ∑ k ∈ Finset.range (M + 1), ((2 * (k + 1) * a (k + 1) : ℝ) : ℂ) •
          hermiteFactor i (2 * k + 1) := by
    rw [Finset.sum_range_succ' (fun m => ((a m : ℝ) : ℂ) •
      (((2 * m : ℕ) : ℂ) • hermiteFactor i (2 * m - 1))) M,
      Finset.sum_range_succ (fun k => ((2 * (k + 1) * a (k + 1) : ℝ) : ℂ) •
        hermiteFactor i (2 * k + 1)) M]
    have hzero : ((2 * (M + 1) * a (M + 1) : ℝ) : ℂ) • hermiteFactor i (2 * M + 1) = 0 := by
      rw [ha]
      simp
    rw [hzero, add_zero]
    have hfirst : ((a 0 : ℝ) : ℂ) • (((2 * 0 : ℕ) : ℂ) • hermiteFactor i (2 * 0 - 1)) = 0 := by
      simp
    rw [hfirst, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hidx : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [hidx, smul_smul]
    push_cast
    ring_nf
  rw [hL, hsecond, coordCombo, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  module
