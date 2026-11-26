-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_movingEndpointParameterPackage_epsilon_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:08.764681+00:00
-- url     : https://prove2.me/submissions/7e5a8395-d08c-450c-a17c-74c9b109f622

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Theorems.Thm_FirstPassageLinearTransport_exists_movingEndpointParameterPackage
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrierC0_pos
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
    {Amax c beta N : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c) (hbeta : 0 < beta)
    (hN : 0 < N) :
    ∃ P : MovingEndpointParameterPackage Amax c beta, N < P.epsilon := by
  let P₀ : MovingEndpointParameterPackage Amax c beta :=
    Classical.choice (exists_movingEndpointParameterPackage hAmax hc hbeta)
  let target : ℝ := N + 1
  have htarget0 : 0 < target := by dsimp [target]; linarith
  have htargetN : N < target := by dsimp [target]; linarith
  have hc00 : 0 < maximalBarrierC0 := maximalBarrierC0_pos
  let Dfloor : ℝ := (target + 5 / 2) / maximalBarrierC0 + 2
  have hDfloor1 : 1 < Dfloor := by
    dsimp [Dfloor]
    have hnum : 0 < target + 5 / 2 := by linarith
    have : 0 < (target + 5 / 2) / maximalBarrierC0 :=
      div_pos hnum hc00
    linarith
  let D : ℝ := max P₀.run.D Dfloor
  have hDfloorD : Dfloor ≤ D := by dsimp [D]; exact le_max_right _ _
  have hD1 : 1 < D := hDfloor1.trans_le hDfloorD
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hDquot : (target + 5 / 2) / maximalBarrierC0 < D := by
    dsimp [Dfloor] at hDfloor1 hDfloorD ⊢
    linarith
  have hDsquare : D < D ^ 2 := by nlinarith
  have hDRate : target + 5 / 2 < maximalBarrierC0 * D ^ 2 := by
    have hquotSq : (target + 5 / 2) / maximalBarrierC0 < D ^ 2 :=
      hDquot.trans hDsquare
    simpa [mul_comm] using (div_lt_iff₀ hc00).1 hquotSq
  have htau0 : 0 < P₀.run.tau := P₀.run.pHi.eta_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Cfloor : ℝ := (D / P₀.run.tau) ^ 2 +
    (target + 5 / 2) / Real.log 2 + 2
  have hCfloorD : (D / P₀.run.tau) ^ 2 < Cfloor := by
    dsimp [Cfloor]
    have hrate0 : 0 < (target + 5 / 2) / Real.log 2 := by
      exact div_pos (by linarith) hlog2
    linarith
  have hCfloorRate : (target + 5 / 2) / Real.log 2 < Cfloor := by
    dsimp [Cfloor]
    have hsq0 : 0 ≤ (D / P₀.run.tau) ^ 2 := sq_nonneg _
    linarith
  let Cswitch : ℝ := max P₀.Cswitch Cfloor
  have hOldC : P₀.Cswitch ≤ Cswitch := by
    dsimp [Cswitch]
    exact le_max_left _ _
  have hFloorC : Cfloor ≤ Cswitch := by
    dsimp [Cswitch]
    exact le_max_right _ _
  have hC0 : 0 < Cswitch := P₀.Cswitch_pos.trans_le hOldC
  have hCD : (D / P₀.run.tau) ^ 2 < Cswitch :=
    hCfloorD.trans_le hFloorC
  have hCRate : target + 5 / 2 < Cswitch * Real.log 2 := by
    have hquot : (target + 5 / 2) / Real.log 2 < Cswitch :=
      hCfloorRate.trans_le hFloorC
    exact (div_lt_iff₀ hlog2).1 hquot
  have hcap : D / Real.sqrt Cswitch ≤ P₀.run.tau := by
    have hsqrtC : 0 < Real.sqrt Cswitch := Real.sqrt_pos.2 hC0
    have hleft : 0 ≤ D / P₀.run.tau := (div_pos hD0 htau0).le
    have hroot : D / P₀.run.tau < Real.sqrt Cswitch :=
      (Real.lt_sqrt hleft).2 hCD
    apply (div_le_iff₀ hsqrtC).2
    have hmul := mul_lt_mul_of_pos_left hroot htau0
    have heq : P₀.run.tau * (D / P₀.run.tau) = D := by
      field_simp [ne_of_gt htau0]
    rw [heq] at hmul
    exact hmul.le
  let run : ShrinkingBarrierRunData := { P₀.run with
    D := D
    D_pos := hD0 }
  let P : MovingEndpointParameterPackage Amax c beta := {
    run := run
    Cswitch := Cswitch
    epsilon := target
    K₀ := P₀.K₀
    K₁ := P₀.K₁
    Amax_pos := P₀.Amax_pos
    Cswitch_pos := hC0
    terminal_below_switch := P₀.terminal_below_switch.trans_le hOldC
    high_cap := by simpa [run] using hcap
    high_rate_margin := by
      rw [lt_sub_iff_add_lt, lt_min_iff]
      exact ⟨hCRate, hDRate⟩
    clock_pressure := P₀.clock_pressure
    high_height_contraction := by
      simpa [run] using P₀.high_height_contraction
    tau_lt_beta := by simpa [run] using P₀.tau_lt_beta
    epsilon_pos := htarget0
    K₀_gt_six := P₀.K₀_gt_six
    K₁_pos := P₀.K₁_pos
    K₁_reserve := P₀.K₁_reserve }
  exact ⟨P, by simpa [P] using htargetN⟩
end FirstPassageLinearTransport
