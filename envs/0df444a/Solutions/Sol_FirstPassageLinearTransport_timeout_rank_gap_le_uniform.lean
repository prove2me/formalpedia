-- Prove2me | solution 1 for FirstPassageLinearTransport.timeout_rank_gap_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:04.193285+00:00
-- url     : https://prove2.me/submissions/08a648f7-5aba-4d14-acd2-48a6e5fe76a9

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
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
    {K₀ C : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ)) :
    (m : ℝ) - timeoutTargetRank K₀ L m ≤ C * K₀ / 2 + 1 := by
  let r := movingLowRatio K₀ L
  let q := timeoutTargetRank K₀ L m
  have hLR : 0 < (L : ℝ) := by positivity
  have hq : r * (m : ℝ) - 1 < (q : ℝ) := by
    simpa [r, q, timeoutTargetRank] using
      (Nat.sub_one_lt_floor (movingLowRatio K₀ L * (m : ℝ)))
  have hscale : K₀ * (m : ℝ) / (2 * (L : ℝ)) ≤ C * K₀ / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hmC hK₀
    rw [div_le_iff₀ (show 0 < (2 : ℝ) * (L : ℝ) by positivity)]
    nlinarith
  dsimp [r] at hq
  unfold movingLowRatio at hq
  change (m : ℝ) - (q : ℝ) ≤ C * K₀ / 2 + 1
  have hrw :
      (1 - K₀ / (2 * (L : ℝ))) * (m : ℝ) =
        (m : ℝ) - K₀ * (m : ℝ) / (2 * (L : ℝ)) := by
    field_simp
  rw [hrw] at hq
  nlinarith
end FirstPassageLinearTransport
