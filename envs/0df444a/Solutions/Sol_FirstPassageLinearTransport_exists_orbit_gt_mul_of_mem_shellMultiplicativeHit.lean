-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_orbit_gt_mul_of_mem_shellMultiplicativeHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:05.934929+00:00
-- url     : https://prove2.me/submissions/3ff35ada-9be4-463d-9a62-b2fd63afa64b

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_exists_multiplicative_prefix_gt_of_crosses
import Theorems.Thm_FirstPassageLinearTransport_pure_multiplicative_le_orbit
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
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M n : ℕ} {u : ℝ} (hn : n ∈ shellMultiplicativeHit M u) :
    ∃ j : ℕ, j ≤ M ∧ u * (n : ℝ) < (orbit j n : ℝ) := by
  classical
  have hnFilter := Finset.mem_filter.mp hn
  have hnShell : n ∈ dyadicShell M := hnFilter.1
  have hcross :
      crossesMultiplicativeFrom u M 1 (boolParityWord M n) := hnFilter.2
  obtain ⟨j, hjM, hj⟩ :=
    exists_multiplicative_prefix_gt_of_crosses hcross
  have hnPosNat : 0 < n := by
    have hnLower : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
    exact (pow_pos (by omega) M).trans_le hnLower
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have hscaled := mul_lt_mul_of_pos_right hj hnPos
  have hscaled' :
      u * (n : ℝ) <
        ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) := by
    simpa using hscaled
  exact ⟨j, hjM, hscaled'.trans_le (pure_multiplicative_le_orbit n j)⟩
end FirstPassageLinearTransport
