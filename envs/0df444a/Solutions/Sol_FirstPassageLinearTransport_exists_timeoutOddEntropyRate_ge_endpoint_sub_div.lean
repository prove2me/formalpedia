-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_timeoutOddEntropyRate_ge_endpoint_sub_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:48.568671+00:00
-- url     : https://prove2.me/submissions/64a21ff2-5787-4aec-9cd6-a1e07e033668

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutDisplacementLoss_pos
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddDisplacement_gt_endpoint_sub_div
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddDisplacement_le_endpoint
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_exists_binaryBarrierRate_endpoint_lipschitz
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
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ D : ℝ, 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        firstPassageEndpointRate - D / (L : ℝ) ≤
          timeoutOddEntropyRate K₀ L m := by
  obtain ⟨C, hC, hLip⟩ := exists_binaryBarrierRate_endpoint_lipschitz
  let D := C * timeoutDisplacementLoss K₀
  have hLoss := timeoutDisplacementLoss_pos hK₀
  refine ⟨D, mul_pos hC hLoss, ?_⟩
  intro L m hL hLm hr0 hr1 hscale
  have hLR : 0 < (L : ℝ) := by positivity
  have hm : 0 < m := hL.trans_le hLm
  have hlower := timeoutOddDisplacement_gt_endpoint_sub_div hK₀ hL hLm
  have hupper := timeoutOddDisplacement_le_endpoint hr0 hr1 hm
  have hlowerHalf :
      firstPassageEndpointDisplacement / 2 ≤
        timeoutOddDisplacement K₀ L m := by
    have hLossDiv :
        timeoutDisplacementLoss K₀ / (L : ℝ) ≤
          firstPassageEndpointDisplacement / 2 := by
      rw [div_le_iff₀ hLR]
      nlinarith
    linarith
  have hTimeoutWindow :
      timeoutOddDisplacement K₀ L m ∈
        Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement :=
    ⟨hlowerHalf, hupper⟩
  have hEndpointWindow :
      firstPassageEndpointDisplacement ∈
        Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement :=
    ⟨by linarith [firstPassageEndpointDisplacement_pos], le_rfl⟩
  have hnorm := hLip
    (timeoutOddDisplacement K₀ L m) hTimeoutWindow
    firstPassageEndpointDisplacement hEndpointWindow
  have hdiffNonneg :
      0 ≤ firstPassageEndpointDisplacement -
        timeoutOddDisplacement K₀ L m := sub_nonneg.mpr hupper
  have hrateError :
      firstPassageEndpointRate - timeoutOddEntropyRate K₀ L m ≤
        C * (firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m) := by
    calc
      firstPassageEndpointRate - timeoutOddEntropyRate K₀ L m ≤
          ‖firstPassageEndpointRate - timeoutOddEntropyRate K₀ L m‖ :=
        le_abs_self _
      _ ≤ C * ‖firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m‖ := by
        simpa [firstPassageEndpointRate, timeoutOddEntropyRate] using hnorm
      _ = C * (firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hdiffNonneg]
  have hdispError :
      firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m <
        timeoutDisplacementLoss K₀ / (L : ℝ) := by
    linarith
  have hscaled :
      C * (firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m) ≤ D / (L : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hdispError hC
    dsimp [D]
    have heq :
        C * (timeoutDisplacementLoss K₀ / (L : ℝ)) =
          (C * timeoutDisplacementLoss K₀) / (L : ℝ) := by ring
    rw [heq] at hmul
    exact hmul.le
  linarith [hrateError.trans hscaled]
end FirstPassageLinearTransport
