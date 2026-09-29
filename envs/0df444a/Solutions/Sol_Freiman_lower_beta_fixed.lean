-- Prove2me | solution 1 for Freiman.lower_beta_fixed
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T13:20:19.440478+00:00
-- url     : https://prove2.me/submissions/222194be-0c5d-41cd-9829-f0cb53d67909

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Freiman

theorem solution : prefixEval [1,3] lowerBeta = lowerBeta := by
  have hs : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hr : 0 ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have hroot : 3 ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have hb : 0 ≤ lowerBeta := by
    dsimp [lowerBeta]
    linarith
  have hquad : lowerBeta ^ 2 + 3 * lowerBeta = 3 := by
    dsimp [lowerBeta]
    nlinarith [hs]
  have hd : (3 : ℝ) + lowerBeta ≠ 0 := ne_of_gt (by linarith)
  have he : (3 : ℝ) + lowerBeta + 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  change 1 / (1 + 1 / (3 + lowerBeta)) = lowerBeta
  rw [one_add_div hd, one_div_div]
  apply (div_eq_iff he).2
  nlinarith [hquad]

#print axioms solution
