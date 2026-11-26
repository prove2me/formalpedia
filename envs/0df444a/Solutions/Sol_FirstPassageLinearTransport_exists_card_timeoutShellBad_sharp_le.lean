-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_card_timeoutShellBad_sharp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:27.459449+00:00
-- url     : https://prove2.me/submissions/83acca36-3a11-48fc-aa92-37b97c4b13e4

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddDisplacement_gt_endpoint_sub_div
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddDisplacement_le_endpoint
import Theorems.Thm_FirstPassageLinearTransport_card_timeoutShellBad_le_binomialUpperTail
import Theorems.Thm_P2M_FirstPassageLinearTransport_timeoutEndpointT__pos_c56393fbdaca
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_exists_normalized_binomialUpperTail_le_binaryBarrierRate
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_lt_quarter
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_pos
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
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
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ K₀ : ℝ, ∀ L m : ℕ,
        0 ≤ K₀ → 0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          (C / Real.sqrt m) *
            Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_normalized_binomialUpperTail_le_binaryBarrierRate
      timeoutEndpointT₀_pos
  refine ⟨C, hC, ?_⟩
  intro K₀ L m hK₀ hL hLm hr0 hr1 hscale
  let k := timeoutOddThreshold (timeoutTargetRank K₀ L m)
  have hm : 0 < m := hL.trans_le hLm
  have hmR : 0 < (m : ℝ) := by positivity
  have hdispLower :=
    timeoutOddDisplacement_gt_endpoint_sub_div hK₀ hL hLm
  have hdispUpper := timeoutOddDisplacement_le_endpoint hr0 hr1 hm
  have hLR : 0 < (L : ℝ) := by positivity
  have hLossDiv :
      timeoutDisplacementLoss K₀ / (L : ℝ) ≤
        firstPassageEndpointDisplacement / 2 := by
    rw [div_le_iff₀ hLR]
    nlinarith
  have hdispHalf :
      firstPassageEndpointDisplacement / 2 ≤
        timeoutOddDisplacement K₀ L m := by
    linarith
  have hratioLower :
      1 / 2 + firstPassageEndpointDisplacement / 2 ≤
        (k : ℝ) / (m : ℝ) := by
    simpa [timeoutOddDisplacement, k, add_comm] using
      add_le_add_left hdispHalf (1 / 2)
  have hratioUpper : (k : ℝ) / (m : ℝ) < 3 / 4 := by
    have hquarter := firstPassageEndpointDisplacement_lt_quarter
    have hraw :
        (k : ℝ) / (m : ℝ) - 1 / 2 ≤
          firstPassageEndpointDisplacement := by
      simpa [timeoutOddDisplacement, k] using hdispUpper
    linarith
  have hgap :
      (m : ℝ) * (1 / 2 + timeoutEndpointT₀) ≤ (k : ℝ) := by
    have ht₀ : timeoutEndpointT₀ ≤
        firstPassageEndpointDisplacement / 2 := by
      unfold timeoutEndpointT₀
      linarith [firstPassageEndpointDisplacement_pos]
    have ht₀' : 1 / 2 + timeoutEndpointT₀ ≤
        1 / 2 + firstPassageEndpointDisplacement / 2 := by
      simpa [add_comm] using add_le_add_left ht₀ (1 / 2)
    rw [mul_comm]
    exact (le_div_iff₀ hmR).1
      (ht₀'.trans hratioLower)
  have hk : 0 < k := by
    have hpositive : 0 < (m : ℝ) * (1 / 2 + timeoutEndpointT₀) := by
      exact mul_pos hmR (by linarith [timeoutEndpointT₀_pos])
    have hkR : 0 < (k : ℝ) := lt_of_lt_of_le hpositive hgap
    exact_mod_cast hkR
  have hklt : k < m := by
    have hratioOne : (k : ℝ) / (m : ℝ) < 1 :=
      hratioUpper.trans (by norm_num)
    have hkR : (k : ℝ) < (m : ℝ) := by
      rwa [div_lt_one hmR] at hratioOne
    exact_mod_cast hkR
  have hkLower : (m : ℝ) / 4 ≤ (k : ℝ) := by
    have hhalf : (1 / 2 : ℝ) ≤
        1 / 2 + firstPassageEndpointDisplacement / 2 := by
      linarith [firstPassageEndpointDisplacement_pos]
    have hratioQuarter : (1 / 4 : ℝ) ≤ (k : ℝ) / (m : ℝ) := by
      linarith [hhalf.trans hratioLower]
    have hscaled := (le_div_iff₀ hmR).1 hratioQuarter
    calc
      (m : ℝ) / 4 = (1 / 4 : ℝ) * (m : ℝ) := by ring
      _ ≤ (k : ℝ) := hscaled
  have hmkLower :
      (m : ℝ) / 4 ≤ ((m - k : ℕ) : ℝ) := by
    have hkThreeQuarter : (k : ℝ) < 3 * (m : ℝ) / 4 := by
      rw [div_lt_iff₀ hmR] at hratioUpper
      nlinarith
    have hsubCast : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hklt.le]
    rw [hsubCast]
    linarith
  have hcount := card_timeoutShellBad_le_binomialUpperTail
    (K₀ := K₀) (L := L) (m := m) hklt.le
  have hcountR :
      ((timeoutShellBad K₀ L m).card : ℝ) ≤
        (binomialUpperTail m k : ℝ) := by exact_mod_cast hcount
  have hpow : 0 < (2 : ℝ) ^ m := by positivity
  calc
    ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
        (binomialUpperTail m k : ℝ) / (2 : ℝ) ^ m :=
      (div_le_div_iff_of_pos_right hpow).2 hcountR
    _ ≤ (C / Real.sqrt m) *
          Real.exp (-((m : ℝ) *
            binaryBarrierRate ((k : ℝ) / (m : ℝ) - 1 / 2))) :=
      htail m k hm hk hklt hgap hkLower hmkLower
    _ = (C / Real.sqrt m) *
          Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) := by
      rfl
end FirstPassageLinearTransport
