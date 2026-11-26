-- Prove2me | solution 1 for FirstPassageLinearTransport.not_hasTargetHeightWitness_of_prefix_crossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:38.882173+00:00
-- url     : https://prove2.me/submissions/345a9207-7407-43e6-b9f1-a13d625c6ce4

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_orbit_lower_by_halving
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_exists_multiplicative_prefix_gt_of_crosses
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_pure_multiplicative_le_orbit
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {h n : ℕ} {u : ℝ} {f : ℕ → ℝ}
    (hn : 0 < n)
    (htarget : f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hcross : crossesMultiplicativeFrom u h 1 (boolParityWord h n)) :
    ¬HasTargetHeightWitness f u n := by
  intro hwitness
  obtain ⟨k, hkTarget, hkHeight⟩ := hwitness
  have hhk : h < k := by
    by_contra hnot
    have hkh : k ≤ h := Nat.le_of_not_gt hnot
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hkh
    have hdiv :
        (n : ℝ) / (2 : ℝ) ^ h ≤ (n : ℝ) / (2 : ℝ) ^ k :=
      (div_le_div_iff_of_pos_left hnPos (by positivity) (by positivity)).2 hpow
    have hlower := orbit_lower_by_halving n k
    linarith
  obtain ⟨j, hjh, hj⟩ :=
    exists_multiplicative_prefix_gt_of_crosses hcross
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscaled := mul_lt_mul_of_pos_right hj hnPos
  have hscaled' :
      u * (n : ℝ) <
        ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) := by
    simpa using hscaled
  have hjHigh := hscaled'.trans_le (pure_multiplicative_le_orbit n j)
  exact (not_lt_of_ge (hkHeight j (hjh.trans hhk.le))) hjHigh
end FirstPassageLinearTransport
