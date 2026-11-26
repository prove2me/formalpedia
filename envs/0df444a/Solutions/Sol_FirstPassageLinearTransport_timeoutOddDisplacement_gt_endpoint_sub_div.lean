-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddDisplacement_gt_endpoint_sub_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:39.138205+00:00
-- url     : https://prove2.me/submissions/7b7ea31b-6452-40d3-838a-59f2f9e40056

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddThreshold_real_lower
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_endpoint_probability_eq_logThreeTwo
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
theorem _root_.solution
    {K₀ : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L) (hLm : L ≤ m) :
    firstPassageEndpointDisplacement -
        timeoutDisplacementLoss K₀ / (L : ℝ) <
      timeoutOddDisplacement K₀ L m := by
  let r := movingLowRatio K₀ L
  let q := timeoutTargetRank K₀ L m
  let k := timeoutOddThreshold q
  have hLR : 0 < (L : ℝ) := by positivity
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast hL.trans_le hLm
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  have hq : r * (m : ℝ) - 1 < (q : ℝ) := by
    simpa [r, q, timeoutTargetRank] using
      (Nat.sub_one_lt_floor (movingLowRatio K₀ L * (m : ℝ)))
  have hk : (q : ℝ) * logThreeTwo - 1 < (k : ℝ) := by
    simpa [k] using timeoutOddThreshold_real_lower q
  have hcombined :
      logThreeTwo * (r * (m : ℝ) - 1) - 1 < (k : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hq hp
    nlinarith [hmul, hk]
  have hnormalized :
      logThreeTwo * r - (logThreeTwo + 1) / (m : ℝ) <
        (k : ℝ) / (m : ℝ) := by
    rw [lt_div_iff₀ hmR]
    calc
      (logThreeTwo * r - (logThreeTwo + 1) / (m : ℝ)) * (m : ℝ) =
          logThreeTwo * (r * (m : ℝ) - 1) - 1 := by
            field_simp
            ring
      _ < (k : ℝ) := hcombined
  have hinv : 1 / (m : ℝ) ≤ 1 / (L : ℝ) := by
    exact one_div_le_one_div_of_le hLR (by exact_mod_cast hLm)
  have hpOne : 0 ≤ logThreeTwo + 1 := by positivity
  have herror :
      (logThreeTwo + 1) / (m : ℝ) ≤
        (logThreeTwo + 1) / (L : ℝ) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hpOne
  have hendpoint :
      firstPassageEndpointDisplacement = logThreeTwo - 1 / 2 := by
    linarith [endpoint_probability_eq_logThreeTwo]
  rw [timeoutOddDisplacement, timeoutDisplacementLoss, hendpoint]
  dsimp [r] at hnormalized
  unfold movingLowRatio at hnormalized
  have hKterm : 0 ≤ logThreeTwo * K₀ := mul_nonneg hp.le hK₀
  calc
    logThreeTwo - 1 / 2 -
          (logThreeTwo * K₀ / 2 + logThreeTwo + 1) / (L : ℝ)
        ≤ logThreeTwo * (1 - K₀ / (2 * (L : ℝ))) -
            (logThreeTwo + 1) / (m : ℝ) - 1 / 2 := by
          have hsplit :
              (logThreeTwo * K₀ / 2 + logThreeTwo + 1) / (L : ℝ) =
                logThreeTwo * K₀ / (2 * (L : ℝ)) +
                  (logThreeTwo + 1) / (L : ℝ) := by ring
          have hrw :
              logThreeTwo * (1 - K₀ / (2 * (L : ℝ))) =
                logThreeTwo - logThreeTwo * K₀ / (2 * (L : ℝ)) := by ring
          rw [hsplit]
          rw [hrw]
          nlinarith [herror]
    _ < (k : ℝ) / (m : ℝ) - 1 / 2 := by
      linarith
end FirstPassageLinearTransport
