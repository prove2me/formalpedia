-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.bijProb_isEquivalent_stirling
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:29:00.304873+00:00
-- url     : https://prove2.me/submissions/648bf848-f096-40f2-a316-59c98feb95ca

-- Generated from ChapterBijectionProbability.lean — solution of BookProof.ChapterBijectionProbability.bijProb_isEquivalent_stirling
import Mathlib
import Definitions.Def_ChapterBijectionProbability
open BookProof.ChapterBijectionProbability



open scoped Nat
open Filter Asymptotics

set_option maxHeartbeats 1000000 in
theorem solution :
    IsEquivalent atTop bijProb
      (fun n => Real.sqrt (2 * n * Real.pi) * Real.exp (-(n : ℝ))) := by

  have hb : bijProb = (fun n : ℕ => (n ! : ℝ)) / (fun n : ℕ => (n : ℝ) ^ n) := rfl
  rw [hb]
  have hstir := Stirling.factorial_isEquivalent_stirling
  have hpow : IsEquivalent atTop (fun n : ℕ => (n : ℝ) ^ n) (fun n : ℕ => (n : ℝ) ^ n) :=
    IsEquivalent.refl
  refine (hstir.div hpow).congr_right ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnn : ((n : ℝ) ^ n) ≠ 0 := pow_ne_zero _ hn0
  simp only [Pi.div_apply]
  rw [mul_div_assoc]
  congr 1
  rw [div_pow, div_right_comm, div_self hnn, one_div, Real.exp_one_pow, ← Real.exp_neg]
