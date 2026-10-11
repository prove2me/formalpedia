-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.pderiv_coordCombo_even
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:49.123171+00:00
-- url     : https://prove2.me/submissions/060060a1-e8f3-410a-bda5-fffef4a90700

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.pderiv_coordCombo_even
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_GaussCoordCombo_pderiv_hermiteFactor_self
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : ℕ → ℝ) (M : ℕ) (ha : a (M + 1) = 0) :
    pderiv i (coordCombo i a 0 M) = coordCombo i (fun k => 2 * (k + 1) * a (k + 1)) 1 M := by

  have hL : pderiv i (coordCombo i a 0 M)
      = ∑ m ∈ Finset.range (M + 1),
          ((a m : ℝ) : ℂ) • (((2 * m : ℕ) : ℂ) • hermiteFactor i (2 * m - 1)) := by
    rw [coordCombo, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Derivation.map_smul]
    congr 1
    cases m with
    | zero => simp [hermiteFactor_zero]
    | succ l =>
        have hidx : 2 * (l + 1) = (2 * l + 1) + 1 := by omega
        have hidx' : 2 * (l + 1) - 1 = 2 * l + 1 := by omega
        rw [hidx, pderiv_hermiteFactor_self]
        norm_num
  rw [hL]
  rw [Finset.sum_range_succ' (fun m => ((a m : ℝ) : ℂ) •
    (((2 * m : ℕ) : ℂ) • hermiteFactor i (2 * m - 1))) M, coordCombo,
    Finset.sum_range_succ (fun k => ((2 * (k + 1) * a (k + 1) : ℝ) : ℂ) •
      hermiteFactor i (2 * k + 1)) M]
  have hzero : ((2 * (M + 1) * a (M + 1) : ℝ) : ℂ) • hermiteFactor i (2 * M + 1) = 0 := by
    rw [ha]; simp
  have hfirst : ((a 0 : ℝ) : ℂ) • (((2 * 0 : ℕ) : ℂ) • hermiteFactor i (2 * 0 - 1)) = 0 := by
    simp
  rw [hzero, add_zero, hfirst, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hidx : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hidx, smul_smul]
  push_cast
  ring_nf
