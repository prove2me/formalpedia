-- Prove2me | solution 1 for FirstPassageLinearTransport.stageMap_rpow_one_add_eta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:51.062991+00:00
-- url     : https://prove2.me/submissions/c653f888-a7ab-4a23-97ba-cd0ea6c8c62a

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
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
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageMap_le_power
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
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    (stageMap p n : ℝ) ^ (1 + eta) ≤
      stageK p ^ 2 * (n : ℝ) ^ (1 + eta) := by
  have hstage := stageMap_le_power p hn hnW
  have hexp0 : 0 ≤ 1 + eta := by linarith [p.eta_pos]
  have hraise :
      (stageMap p n : ℝ) ^ (1 + eta) ≤
        (stageK p * (n : ℝ) ^ r) ^ (1 + eta) :=
    Real.rpow_le_rpow (by positivity) hstage hexp0
  have hKexp : stageK p ^ (1 + eta) ≤ stageK p ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (stageK_one_le p)
      (by linarith [p.eta_le_one])
  have hK : stageK p ^ (1 + eta) ≤ stageK p ^ 2 := by
    simpa [Real.rpow_two] using hKexp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrexp : r * (1 + eta) ≤ 1 + eta := by
    nlinarith [p.r_lt_one.le, p.eta_pos]
  have hnPow : (n : ℝ) ^ (r * (1 + eta)) ≤
      (n : ℝ) ^ (1 + eta) :=
    Real.rpow_le_rpow_of_exponent_le hnOne hrexp
  calc
    (stageMap p n : ℝ) ^ (1 + eta) ≤
        (stageK p * (n : ℝ) ^ r) ^ (1 + eta) := hraise
    _ = stageK p ^ (1 + eta) *
        ((n : ℝ) ^ r) ^ (1 + eta) := by
      rw [Real.mul_rpow (stageK_pos p).le (by positivity)]
    _ = stageK p ^ (1 + eta) *
        (n : ℝ) ^ (r * (1 + eta)) := by
      rw [← Real.rpow_mul (by positivity)]
    _ ≤ stageK p ^ 2 * (n : ℝ) ^ (1 + eta) :=
      mul_le_mul hK hnPow (by positivity) (by positivity)
end FirstPassageLinearTransport
