-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_le_stageClock_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:16:12.462944+00:00
-- url     : https://prove2.me/submissions/f2c4df83-425b-45a0-85d3-1f628a8adf53

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_one_add_eta_of_le_stageLength
import Theorems.Thm_FirstPassageLinearTransport_stageMap_rpow_one_add_eta_le
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_add
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageMap_is_actual
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
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {R n j : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R)
    (hj : j ≤ stageClock p R n) :
    (orbit j n : ℝ) ≤
      stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := by
  induction R generalizing n j with
  | zero =>
      have hj0 : j = 0 := by simpa using hj
      subst j
      rw [orbit_zero]
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (n : ℝ) ^ (1 + eta) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [p.eta_pos])
        _ = stageK p ^ (2 * 0) * (n : ℝ) ^ (1 + eta) := by simp
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW : n ∈ extendedWindow p := hnSet.1
      have hmapSet : stageMap p n ∈ bootstrapSet p R := hnSet.2
      by_cases hjlen : j ≤ stageLength p n
      · have hblock := orbit_le_one_add_eta_of_le_stageLength p hn hnW hjlen
        have hfactor : (1 : ℝ) ≤ stageK p ^ (2 * (R + 1)) :=
          one_le_pow₀ (stageK_one_le p)
        exact hblock.trans (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hfactor
              (Real.rpow_nonneg (by positivity) (1 + eta)))
      · let q := j - stageLength p n
        have hjform : j = stageLength p n + q := by
          dsimp [q]
          omega
        have hqclock : q ≤ stageClock p R (stageMap p n) := by
          rw [stageClock_succ] at hj
          dsimp [q]
          omega
        have hmapPos : 0 < stageMap p n := by
          rw [stageMap_is_actual]
          exact orbit_pos hn _
        have hIH := ih hmapPos hmapSet hqclock
        have hmapPow := stageMap_rpow_one_add_eta_le p hn hnW
        rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
        calc
          (orbit q (stageMap p n) : ℝ) ≤
              stageK p ^ (2 * R) *
                (stageMap p n : ℝ) ^ (1 + eta) := hIH
          _ ≤ stageK p ^ (2 * R) *
                (stageK p ^ 2 * (n : ℝ) ^ (1 + eta)) :=
            mul_le_mul_of_nonneg_left hmapPow
              (pow_nonneg (stageK_pos p).le _)
          _ = stageK p ^ (2 * (R + 1)) *
                (n : ℝ) ^ (1 + eta) := by
            rw [show 2 * (R + 1) = 2 * R + 2 by omega, pow_add]
            ring
end FirstPassageLinearTransport
