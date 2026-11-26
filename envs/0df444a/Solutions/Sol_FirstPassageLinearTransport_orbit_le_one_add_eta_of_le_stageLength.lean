-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_le_one_add_eta_of_le_stageLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:23:12.29704+00:00
-- url     : https://prove2.me/submissions/0688cd32-8a81-46a6-b9ea-2ac2906b2388

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
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_rho_pow
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_rho_lt_one
import Theorems.Thm_FirstPassageLinearTransport_rho_pos
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_log
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
    {r eta : ℝ} (p : StageSetup r eta) {n j : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hj : j ≤ stageLength p n) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + eta) := by
  by_cases hlarge : p.M0 ≤ Nat.log 2 n
  · have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
    have hjlog : j ≤ Nat.log 2 n :=
      hj.trans (stageLength_le_log p hn hnW)
    have henv := (hgood j hjlog).2
    have hscale : centralOrbitScale j ≤ 1 := by
      rw [centralOrbitScale_eq_rho_pow]
      exact pow_le_one₀ rho_pos.le rho_lt_one.le
    exact henv.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hscale
          (Real.rpow_nonneg (by positivity) (1 + eta)))
  · have hlen : stageLength p n = 0 := by
      simp [stageLength, hlarge]
    have hj0 : j = 0 := by omega
    subst j
    rw [orbit_zero]
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (1 + eta) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [p.eta_pos])
end FirstPassageLinearTransport
