-- Prove2me | solution 1 for FirstPassageLinearTransport.rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:04.180585+00:00
-- url     : https://prove2.me/submissions/5c5de9b6-bd6a-4ab7-bb8c-f85a5e1b419a

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawTime_prefix_cases
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_add_one_eq_two_mul
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_mem
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_le
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_mem
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_le
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_landingBand
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
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit
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


attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k : ℕ} {z : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z) :
    rawFirstPassageTime n z =
        rawTime n (shortcutFirstPassageTime n z) ∧
      rawOrbit (rawFirstPassageTime n z) n =
        orbit (shortcutFirstPassageTime n z) n := by
  let tau := shortcutFirstPassageTime n z
  let ell := rawTime n tau
  have htauMem0 := shortcutFirstPassageTime_mem hk
  have htauMem : (orbit tau n : ℝ) ≤ z := by simpa [tau] using htauMem0
  have hellMem : (rawOrbit ell n : ℝ) ≤ z := by
    simpa [ell, rawOrbit_rawTime_eq_orbit] using htauMem
  have hrawLe : rawFirstPassageTime n z ≤ ell :=
    rawFirstPassageTime_le hellMem
  have hband0 := shortcutFirstPassageTime_landingBand hzStart hk
  have hband : z < 2 * (orbit tau n : ℝ) ∧
      (orbit tau n : ℝ) ≤ z := by simpa [tau] using hband0
  have hnoEarlier : ∀ i : ℕ, i < ell → z < (rawOrbit i n : ℝ) := by
    intro i hi
    have hiLe : i ≤ rawTime n tau := by simpa [ell] using hi.le
    rcases rawTime_prefix_cases hiLe with ⟨j, hjtau, hcase⟩
    rcases hcase with hcorresponding | hintermediate
    · have hjlt : j < tau := by
        by_contra hnot
        have hjEq : j = tau := Nat.le_antisymm hjtau (le_of_not_gt hnot)
        subst j
        subst i
        simpa [ell] using hi
      have habove : z < (orbit j n : ℝ) := by
        by_contra hnot
        have hle : (orbit j n : ℝ) ≤ z := le_of_not_gt hnot
        have htauLe0 := shortcutFirstPassageTime_le hle
        have htauLe : tau ≤ j := by simpa [tau] using htauLe0
        omega
      subst i
      simpa [rawOrbit_rawTime_eq_orbit] using habove
    · rcases hintermediate with ⟨hjlt, hodd, hiEq⟩
      have hjNext : j + 1 ≤ tau := by omega
      have habove : z < 2 * (orbit (j + 1) n : ℝ) := by
        rcases lt_or_eq_of_le hjNext with hjNextLt | hjNextEq
        · have hnextAbove : z < (orbit (j + 1) n : ℝ) := by
            by_contra hnot
            have hle : (orbit (j + 1) n : ℝ) ≤ z := le_of_not_gt hnot
            have htauLe0 := shortcutFirstPassageTime_le hle
            have htauLe : tau ≤ j + 1 := by simpa [tau] using htauLe0
            omega
          have hnextPos : 0 < orbit (j + 1) n := orbit_pos hn _
          have hnextPosR : (0 : ℝ) < orbit (j + 1) n := by exact_mod_cast hnextPos
          nlinarith
        · simpa [hjNextEq] using hband.1
      subst i
      rw [rawOrbit_rawTime_add_one_eq_two_mul hodd]
      exact_mod_cast habove
  have hellLe : ell ≤ rawFirstPassageTime n z := by
    by_contra hnot
    have hlt : rawFirstPassageTime n z < ell := lt_of_not_ge hnot
    have habove := hnoEarlier _ hlt
    have hmem := rawFirstPassageTime_mem hellMem
    exact (not_le_of_gt habove) hmem
  have heq : rawFirstPassageTime n z = ell :=
    Nat.le_antisymm hrawLe hellLe
  constructor
  · simpa [ell] using heq
  · rw [heq]
    simpa [ell] using rawOrbit_rawTime_eq_orbit n tau
end FirstPassageLinearTransport
