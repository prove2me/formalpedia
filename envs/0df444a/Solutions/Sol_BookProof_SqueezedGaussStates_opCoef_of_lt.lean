-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.opCoef_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:50.488394+00:00
-- url     : https://prove2.me/submissions/6f8e183f-e337-470c-adc8-14a4bffd41de

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.opCoef_of_lt
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_SqueezedGaussStates_sqCoef_of_le
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (α γ v : ℝ) {M k : ℕ} (hk : k < M) :
    opCoef α γ v M k = kappa α γ v * sqCoef v M k := by

  have h1 : sqCoef v M k = v ^ k / (k.factorial : ℝ) := sqCoef_of_le (by omega)
  have h2 : sqCoef v M (k + 1) = v ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    sqCoef_of_le (by omega)
  have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hpos : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [opCoef, kappa, h1, h2, hfac]
  field_simp
  ring
