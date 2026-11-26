-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_movingEndpointParameterPackage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:05.97168+00:00
-- url     : https://prove2.me/submissions/f5518784-b82d-4b7c-870c-31c2dd0ca2c8

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_exists_shrinkingPolylogParameterPackage
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
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
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
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c) (hbeta : 0 < beta) :
    Nonempty (MovingEndpointParameterPackage Amax c beta) := by
  let Aaux := max Amax timeSupportCriticalExponent + 1
  have hAaux : timeSupportCriticalExponent < Aaux := by
    dsimp [Aaux]
    linarith [le_max_right Amax timeSupportCriticalExponent]
  have hAmaxAux : Amax < Aaux := by
    dsimp [Aaux]
    linarith [le_max_left Amax timeSupportCriticalExponent]
  let Q : ShrinkingPolylogParameterPackage Aaux c beta :=
    Classical.choice
      (exists_shrinkingPolylogParameterPackage hAaux hc hbeta)
  let K₀ : ℝ := 7
  let K₁ : ℝ := 8 / driftGap
  have hK₁ : 0 < K₁ := by
    dsimp [K₁]
    exact div_pos (by norm_num) driftGap_pos
  have hreserve : 8 ≤ K₁ * driftGap := by
    dsimp [K₁]
    field_simp [ne_of_gt driftGap_pos]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterminal : Amax / Real.log 2 < Q.Cswitch := by
    exact (div_lt_div_iff_of_pos_right hlog2).2 hAmaxAux |>.trans
      Q.terminal_below_switch
  have hclock : 1 / driftGap < c * Real.log 2 := by
    have hprod : 1 < c * (driftGap * Real.log 2) := by
      exact (div_lt_iff₀ (mul_pos driftGap_pos hlog2)).1
        (by simpa [fixedPolylogClockCritical] using hc)
    rw [div_lt_iff₀ driftGap_pos]
    nlinarith
  exact ⟨{
    run := Q.run
    Cswitch := Q.Cswitch
    epsilon := Q.kappa
    K₀ := K₀
    K₁ := K₁
    Amax_pos := hAmax
    Cswitch_pos := Q.Cswitch_pos
    terminal_below_switch := hterminal
    high_cap := Q.high_cap
    high_rate_margin := Q.high_rate_margin
    clock_pressure := hclock
    high_height_contraction := Q.high_height_contraction
    tau_lt_beta := Q.tau_lt_beta
    epsilon_pos := Q.kappa_pos
    K₀_gt_six := by norm_num [K₀]
    K₁_pos := hK₁
    K₁_reserve := hreserve }⟩
end FirstPassageLinearTransport
