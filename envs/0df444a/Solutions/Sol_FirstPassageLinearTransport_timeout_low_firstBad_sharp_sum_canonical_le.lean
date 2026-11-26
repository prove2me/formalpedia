-- Prove2me | solution 1 for FirstPassageLinearTransport.timeout_low_firstBad_sharp_sum_canonical_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:48.76406+00:00
-- url     : https://prove2.me/submissions/86e9c5ed-ee92-41e8-9b9b-b38588d10d78

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_density_le
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_sharp_entropy_tail_exact_rate_Icc_le
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 2 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ p ∈ Finset.Icc (L + 1) S,
      ((((p + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H C b₀ b : ℝ}
    (hTimes : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        (C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hC : 0 ≤ C) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ∑ p ∈ Finset.Icc (L + 1) S,
        ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) *
        exactSharpCriticalLowSeriesConstant b₀ C *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
  have hterm : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * C *
          (((p + 1 : ℕ) : ℝ) /
            Real.sqrt ((p - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := by
    intro p hpI
    have hpI' := Finset.mem_Icc.mp hpI
    have hp1 : 1 ≤ p := by omega
    have hpM : p < M := hpI'.2.trans_lt hSM
    have hbase := timeoutFirstBadSourcesAtRank_density_le
      (S := S) hrStar hStarHi hStarLo hM hp1
      (hnextPos p hpI) (hnextLt p hpI) hpM (hsmall p hpI)
      (hTimes p hpI) (hTarget p hpI)
    calc
      _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) *
          ((C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := hbase
      _ = _ := by ring
  have htail := sharp_entropy_tail_exact_rate_Icc_le hb₀ hb₀b
    (show 2 ≤ L + 1 by omega) hLS
  have htail' :
      ∑ p ∈ Finset.Icc (L + 1) S,
          ((p + 1 : ℕ) : ℝ) / Real.sqrt ((p - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) ≤
        3 * Real.sqrt ((L : ℝ) + 1) *
          Real.exp (-(b * (((L + 1) - 1 : ℕ) : ℝ))) *
            weightedTailConstant b₀ (b₀ / 2) := by
    simpa [Nat.cast_add, Nat.cast_one] using htail
  have hconst : 3 * C * weightedTailConstant b₀ (b₀ / 2) ≤
      exactSharpCriticalLowSeriesConstant b₀ C := by
    unfold exactSharpCriticalLowSeriesConstant
    have hle := le_max_right
      (weightedTailConstant (Real.log 2) (Real.log 2 / 2))
      (3 * C * weightedTailConstant b₀ (b₀ / 2))
    linarith
  have hH0 : 0 ≤ H := by
    have hcard0 : 0 ≤
        ((timeoutFeasibleTimes P K₀ L M S (L + 1)).card : ℝ) := by positivity
    exact hcard0.trans
      (hTimes (L + 1) (Finset.mem_Icc.mpr ⟨le_rfl, hLS⟩))
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) * C := by positivity
  calc
    _ ≤ ∑ p ∈ Finset.Icc (L + 1) S,
        H * (1 + 6 / (rStar : ℝ)) * C *
          (((p + 1 : ℕ) : ℝ) / Real.sqrt ((p - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) :=
      Finset.sum_le_sum hterm
    _ = H * (1 + 6 / (rStar : ℝ)) * C *
        (∑ p ∈ Finset.Icc (L + 1) S,
          ((p + 1 : ℕ) : ℝ) / Real.sqrt ((p - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ H * (1 + 6 / (rStar : ℝ)) * C *
        (3 * Real.sqrt (L + 1) *
          Real.exp (-(b * (((L + 1) - 1 : ℕ) : ℝ))) *
            weightedTailConstant b₀ (b₀ / 2)) :=
      mul_le_mul_of_nonneg_left htail' hcoef0
    _ = H * (1 + 6 / (rStar : ℝ)) *
        (3 * C * weightedTailConstant b₀ (b₀ / 2)) *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
      rw [show L + 1 - 1 = L by omega]
      ring
    _ ≤ H * (1 + 6 / (rStar : ℝ)) *
        exactSharpCriticalLowSeriesConstant b₀ C *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
      have hfactor0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) := by positivity
      have htail0 : 0 ≤ Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ))) := by
        positivity
      gcongr
    _ = _ := by ring
end FirstPassageLinearTransport
