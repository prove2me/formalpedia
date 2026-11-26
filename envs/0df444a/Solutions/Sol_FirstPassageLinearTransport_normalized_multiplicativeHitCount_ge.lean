-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_multiplicativeHitCount_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:55.711019+00:00
-- url     : https://prove2.me/submissions/8140528d-a073-4101-9e95-6d378c97e01f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_threeQuarterLowerTailMass_le
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedTree_upper
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_safeTerminalSum_le_lowerTail
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u eps : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r)
    (hterminal : ∀ v : Fin r → Bool,
      ballotWordValue 1 v ≤ u →
        ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r)
    (heps : 0 < eps) :
    (2 / (3 * u)) * (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) ≤
      (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r := by
  have hpow : 0 < (2 : ℝ) ^ r := by positivity
  have htail := threeQuarterLowerTailMass_le heps hr
  have hsafe := safeTerminalSum_le_lowerTail hterminal
  have htree := stoppedTree_upper hu r
  have hsafe' : safeTerminalSum u r 1 ≤
      (2 : ℝ) ^ r * (3 / (16 * eps ^ 2 * (r : ℝ))) :=
    hsafe.trans (mul_le_mul_of_nonneg_left htail hpow.le)
  have hmain : (2 : ℝ) ^ r *
        (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) ≤
      (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) := by
    linarith
  have hscalePos : 0 < 3 * u / 2 := by
    have : 0 < u := zero_lt_one.trans_le hu
    positivity
  have hnorm : 1 - 3 / (16 * eps ^ 2 * (r : ℝ)) ≤
      ((multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r) *
        (3 * u / 2) := by
    have hmain' :
        (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) * (2 : ℝ) ^ r ≤
          (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) := by
      simpa [mul_comm] using hmain
    have hdiv := (le_div_iff₀ hpow).2 hmain'
    calc
      1 - 3 / (16 * eps ^ 2 * (r : ℝ)) ≤
          (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) /
            (2 : ℝ) ^ r := hdiv
      _ = ((multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r) *
          (3 * u / 2) := by ring
  have hdivide := (div_le_iff₀ hscalePos).2 hnorm
  calc
    (2 / (3 * u)) * (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) =
        (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) / (3 * u / 2) := by
      field_simp
    _ ≤ (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r := hdivide
end FirstPassageLinearTransport
