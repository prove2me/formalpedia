-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.orbit_le_start_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:23.394151+00:00
-- url     : https://prove2.me/submissions/b84a08bf-e729-4a78-b1f3-8b51bbdd454f

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_two_pow_mul
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_endpoint_lt_start
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_initialWindowGood_subset_extendedWindow
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
    {P : TimeoutHighRunData} {K₀ beta : ℝ}
    {L M S n elapsed q : ℕ}
    (hbeta : 0 < beta) (htau : P.tau < beta)
    (hLowMargin : 2 * (S : ℝ) ≤ beta * (M : ℝ))
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    {j : ℕ} (hj : j ≤ elapsed) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  have hn : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact hp.trans_le (mem_dyadicShell.mp hnShell).1
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      let p := timeoutHighSetup P M M
      have hnW : n ∈ extendedWindow p :=
        initialWindowGood_subset_extendedWindow p hnGood
      have hlocal := orbit_le_one_add_eta_of_le_stageLength p hn hnW hj
      have heta : timeoutHighTolerance P M M < beta :=
        (timeoutHighTolerance_le_tau P M M).trans_lt htau
      exact hlocal.trans
        (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
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
        have hxle : (orbit elapsed n : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (hrun.endpoint_lt_start hnShell).le
        have heta : timeoutHighTolerance P M m < beta :=
          (timeoutHighTolerance_le_tau P M m).trans_lt htau
        have hbase : (orbit elapsed n : ℝ) ^
            (1 + timeoutHighTolerance P M m) ≤
              (n : ℝ) ^ (1 + timeoutHighTolerance P M m) :=
          Real.rpow_le_rpow (by positivity) hxle
            (by linarith [timeoutHighTolerance_pos P M m])
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (hbase.trans
          (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)))
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
        have hlocal : (orbit v (orbit elapsed n) : ℝ) ≤
            (((2 : ℝ) ^ S) ^ (2 : ℕ)) := by
          exact_mod_cast hlocalNat
        have hExp : (S : ℝ) * 2 ≤ (M : ℝ) * beta := by
          nlinarith
        have htwo : (((2 : ℝ) ^ S) ^ (2 : ℝ)) ≤
            (((2 : ℝ) ^ M) ^ beta) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
        have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
          exact_mod_cast (mem_dyadicShell.mp hnShell).1
        have houter : ((2 : ℝ) ^ M) ^ beta ≤ (n : ℝ) ^ beta :=
          Real.rpow_le_rpow (by positivity) hnLower hbeta.le
        have hfinal : (n : ℝ) ^ beta ≤ (n : ℝ) ^ (1 + beta) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
        have htwo' : (((2 : ℝ) ^ S) ^ (2 : ℕ)) ≤
            (((2 : ℝ) ^ M) ^ beta) := by
          simpa [Real.rpow_two] using htwo
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (htwo'.trans (houter.trans hfinal))
end TimeoutRecertificationRun
end FirstPassageLinearTransport
