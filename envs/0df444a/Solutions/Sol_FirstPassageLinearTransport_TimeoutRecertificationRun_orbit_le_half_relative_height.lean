-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.orbit_le_half_relative_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:01.438511+00:00
-- url     : https://prove2.me/submissions/367c4b37-e94a-491d-903a-4d74b2b41df9

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_two_pow_mul
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_le_initialRank
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_initialWindowGood_subset_extendedWindow
import Theorems.Thm_FirstPassageLinearTransport_initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_add
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_one_add_eta_of_le_stageLength
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
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
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
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
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ R : ℝ}
    {L M S n elapsed q : ℕ}
    (hR : 4 ≤ R)
    (hcontract : (P.rHi : ℝ) * (1 + P.tau) ≤ 1)
    (hLowMargin : 2 * S ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    (hnMax : n ∉ shellMultiplicativeHit M (R / 4))
    {j : ℕ} (hj : j ≤ elapsed) :
    (orbit j n : ℝ) ≤ (n : ℝ) * R / 2 := by
  have hn : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact hp.trans_le (mem_dyadicShell.mp hnShell).1
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfirstHeight :=
    (initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
      hnShell hnMax).1
  have hlater : (n : ℝ) ≤ (n : ℝ) * R / 2 := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      have hstage : stageLength (timeoutHighSetup P M M) n ≤ M :=
        stageLength_le_shell (timeoutHighSetup P M M)
          hM0 hnShell' hnGood
      exact (hfirstHeight j (hj.trans hstage)).le
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood
      hgap ih =>
      by_cases hjPrev : j ≤ elapsed
      · exact ih hjPrev
      · let v := j - elapsed
        have hjForm : j = elapsed + v := by dsimp [v]; omega
        have hv : v ≤ stageLength (timeoutHighSetup P M m)
            (orbit elapsed n) := by dsimp [v]; omega
        have hx : 0 < orbit elapsed n := orbit_pos hn elapsed
        have hxW : orbit elapsed n ∈ extendedWindow (timeoutHighSetup P M m) :=
          initialWindowGood_subset_extendedWindow _ hsourceGood
        have hlocal := orbit_le_one_add_eta_of_le_stageLength
          (timeoutHighSetup P M m) hx hxW hv
        have hqPrevInitial : qPrev ≤ rationalTargetRank P.rHi M :=
          hrun.currentRank_le_initialRank
        have hmInitial : m + 1 ≤ rationalTargetRank P.rHi M := by
          simpa [hmPrev] using hqPrevInitial
        have hxUpperNat : orbit elapsed n ≤
            2 ^ rationalTargetRank P.rHi M := by
          exact (mem_dyadicShell.mp hsourceShell).2.le.trans
            (Nat.pow_le_pow_right (by omega) hmInitial)
        have hxUpper : (orbit elapsed n : ℝ) ≤
            (2 : ℝ) ^ rationalTargetRank P.rHi M := by
          exact_mod_cast hxUpperNat
        have htau0 : 0 ≤ 1 + P.tau := by linarith [P.pHi.eta_pos]
        have htol : timeoutHighTolerance P M m ≤ P.tau :=
          timeoutHighTolerance_le_tau P M m
        have hlocalTau : (orbit elapsed n : ℝ) ^
            (1 + timeoutHighTolerance P M m) ≤
              (orbit elapsed n : ℝ) ^ (1 + P.tau) :=
          Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (show 1 ≤ orbit elapsed n by omega))
            (by linarith)
        have hsourcePow : (orbit elapsed n : ℝ) ^ (1 + P.tau) ≤
            ((2 : ℝ) ^ rationalTargetRank P.rHi M) ^ (1 + P.tau) :=
          Real.rpow_le_rpow (by positivity) hxUpper htau0
        have hr0 : (0 : ℝ) ≤ (P.rHi : ℝ) := P.pHi.r_pos.le
        have hqInitial : (rationalTargetRank P.rHi M : ℝ) ≤
            (P.rHi : ℝ) * (M : ℝ) := by
          exact Nat.floor_le (mul_nonneg hr0 (Nat.cast_nonneg M))
        have hExp : (rationalTargetRank P.rHi M : ℝ) *
            (1 + P.tau) ≤ (M : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right hqInitial htau0
          have hcontractM := mul_le_mul_of_nonneg_right hcontract
            (Nat.cast_nonneg M)
          nlinarith
        have htwo : ((2 : ℝ) ^ rationalTargetRank P.rHi M) ^
            (1 + P.tau) ≤ (2 : ℝ) ^ M := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
        have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
          exact_mod_cast (mem_dyadicShell.mp hnShell).1
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (hlocalTau.trans
          (hsourcePow.trans (htwo.trans (hnLower.trans hlater))))
  | @nextLo elapsed qPrev m hrun hmS hLm hmPrevLo hmPrevHi hsourceShell
      hpass hqpos hqparent hgap ih =>
      by_cases hjPrev : j ≤ elapsed
      · exact ih hjPrev
      · let v := j - elapsed
        have hjForm : j = elapsed + v := by dsimp [v]; omega
        have hv : v ≤ hpass.duration := by dsimp [v]; omega
        have hvm : v ≤ m := hv.trans hpass.duration_le
        have hmSle : m + 1 ≤ S := by omega
        have hpowv : 2 ^ v ≤ 2 ^ S :=
          Nat.pow_le_pow_right (by omega) (hvm.trans (by omega))
        have hxS : orbit elapsed n ≤ 2 ^ S :=
          (mem_dyadicShell.mp hsourceShell).2.le.trans
            (Nat.pow_le_pow_right (by omega) hmSle)
        have hlocalNat : orbit v (orbit elapsed n) ≤ (2 ^ S) ^ 2 := by
          calc
            orbit v (orbit elapsed n) ≤ 2 ^ v * orbit elapsed n :=
              orbit_le_two_pow_mul _ _
            _ ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul hpowv hxS
            _ = (2 ^ S) ^ 2 := by ring
        have hSMpow : (2 ^ S) ^ 2 ≤ 2 ^ M := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
        have hlocalToN : orbit v (orbit elapsed n) ≤ n :=
          hlocalNat.trans (hSMpow.trans hnLowerNat)
        have hlocalToNReal : (orbit v (orbit elapsed n) : ℝ) ≤ n := by
          exact_mod_cast hlocalToN
        rw [hjForm, add_comm, orbit_add]
        exact hlocalToNReal.trans hlater
end TimeoutRecertificationRun
end FirstPassageLinearTransport
