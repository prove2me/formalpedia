-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_shrinkingPolylogParameterPackage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:42.660623+00:00
-- url     : https://prove2.me/submissions/1467cb70-610f-48f2-b28d-2282720fa085

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_pos
import Theorems.Thm_FirstPassageLinearTransport_exists_lowBarrier_rate_margin_of_timeSupportCritical_lt
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_exists_stageSetup
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogClockCritical_pos
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
    {A c beta : ℝ}
    (hA : timeSupportCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    Nonempty (ShrinkingPolylogParameterPackage A c beta) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := fixedPolylogClockCritical_pos.trans hc
  have hcLog : 0 < c * Real.log 2 := mul_pos hc0 hlog2
  have hgapLog : 0 < driftGap * Real.log 2 :=
    mul_pos driftGap_pos hlog2
  have hclockCross : 1 < c * (driftGap * Real.log 2) := by
    have := (div_lt_iff₀ hgapLog).1 hc
    simpa [fixedPolylogClockCritical] using this
  have hInvGap : 1 / (c * Real.log 2) < driftGap := by
    rw [div_lt_iff₀ hcLog]
    nlinarith [hclockCross]
  have hHiInterval : a0 < 1 - 1 / (c * Real.log 2) := by
    unfold driftGap at hInvGap
    linarith
  let rHiCeiling := min (1 - 1 / (c * Real.log 2)) ((a0 + 1) / 2)
  have hSafeInterval : a0 < (a0 + 1) / 2 := by
    linarith [a0_lt_one]
  have hHiInterval' : a0 < rHiCeiling := by
    dsimp [rHiCeiling]
    exact lt_min hHiInterval hSafeInterval
  obtain ⟨rHi, hrHiLower, hrHiUpper⟩ := exists_rat_btwn hHiInterval'
  have hrHiClock : (rHi : ℝ) < 1 - 1 / (c * Real.log 2) :=
    hrHiUpper.trans_le (by
      dsimp [rHiCeiling]
      exact min_le_left _ _)
  have hrHiSafe : (rHi : ℝ) < (a0 + 1) / 2 :=
    hrHiUpper.trans_le (by
      dsimp [rHiCeiling]
      exact min_le_right _ _)
  have hrHiOne : (rHi : ℝ) < 1 := by
    have hinv0 : 0 < 1 / (c * Real.log 2) := by positivity
    linarith [hrHiClock]
  have hrHiPos : (0 : ℝ) < rHi := a0_pos.trans hrHiLower
  have hclock : 1 / (1 - (rHi : ℝ)) < c * Real.log 2 := by
    have hgap : 1 / (c * Real.log 2) < 1 - (rHi : ℝ) := by
      linarith [hrHiClock]
    have hden : 0 < 1 - (rHi : ℝ) := sub_pos.mpr hrHiOne
    rw [div_lt_iff₀ hden]
    have hmul := (div_lt_iff₀ hcLog).1 hgap
    nlinarith
  let dHi : ℝ := min ((rHi : ℝ) - a0) (min beta a0)
  have hdHi : 0 < dHi := by
    rw [lt_min_iff, lt_min_iff]
    exact ⟨sub_pos.mpr hrHiLower, hbeta, a0_pos⟩
  let tau := dHi / 2
  have htau0 : 0 < tau := by dsimp [tau]; positivity
  have htauD : tau < dHi := by dsimp [tau]; linarith
  have htauGap : tau < (rHi : ℝ) - a0 :=
    htauD.trans_le (min_le_left _ _)
  have htauBeta : tau < beta :=
    htauD.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htauA : tau < a0 :=
    htauD.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htauSafe : tau < 1 - (rHi : ℝ) := by
    have hRankSafe : (rHi : ℝ) - a0 < 1 - (rHi : ℝ) := by
      linarith [hrHiSafe]
    exact htauGap.trans hRankSafe
  have hheightContract : (rHi : ℝ) * (1 + tau) < 1 := by
    have hlinear : 1 + tau < 2 - (rHi : ℝ) := by
      linarith [htauSafe]
    have hmul := mul_lt_mul_of_pos_left hlinear hrHiPos
    nlinarith [sq_nonneg ((rHi : ℝ) - 1)]
  let pHi := Classical.choice
    (exists_stageSetup hrHiLower hrHiOne htau0 htauGap)
  obtain ⟨lambdaLo, etaLo, bLo, kappa,
      hlambdaLo0, hlambdaLo1, hetaLo0, hetaLoGap, hetaLoA,
      hbLo0, hbLoRate, hbLoLog, hkappa0, hkappa⟩ :=
    exists_lowBarrier_rate_margin_of_timeSupportCritical_lt hA
  have hLoInterval : a0 + etaLo < 1 := by
    unfold driftGap at hetaLoGap
    linarith
  obtain ⟨rLo, hrLoLower, hrLoUpper⟩ := exists_rat_btwn hLoInterval
  have hrLoA : a0 < (rLo : ℝ) := by linarith [hetaLo0]
  have hetaLoRankGap : etaLo < (rLo : ℝ) - a0 := by linarith
  have hrLoPos : (0 : ℝ) < rLo := a0_pos.trans hrLoA
  let pLo := Classical.choice
    (exists_stageSetup hrLoA hrLoUpper hetaLo0 hetaLoRankGap)
  let rStar : ℚ := min rHi rLo
  have hrStar0 : (0 : ℚ) < rStar := by
    dsimp [rStar]
    rw [lt_min_iff]
    exact ⟨by exact_mod_cast hrHiPos, by exact_mod_cast hrLoPos⟩
  let target : ℝ := |kappa| + 4
  have htarget0 : 0 < target := by dsimp [target]; positivity
  have htargetK : kappa + 5 / 2 < target := by
    dsimp [target]
    linarith [le_abs_self kappa]
  have hc00 : 0 < maximalBarrierC0 := maximalBarrierC0_pos
  let D := target / maximalBarrierC0 + 1
  have hD1 : 1 < D := by
    dsimp [D]
    linarith [div_pos htarget0 hc00]
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hDRate : target < maximalBarrierC0 * D ^ 2 := by
    have hDsq : D < D ^ 2 := by nlinarith
    have hmul : maximalBarrierC0 * D < maximalBarrierC0 * D ^ 2 :=
      mul_lt_mul_of_pos_left hDsq hc00
    have heq : maximalBarrierC0 * D = target + maximalBarrierC0 := by
      dsimp [D]
      field_simp [ne_of_gt hc00]
    rw [heq] at hmul
    linarith
  let Cswitch := (D / tau) ^ 2 + target / Real.log 2 +
    A / Real.log 2 + 3
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA
  have hC0 : 0 < Cswitch := by
    dsimp [Cswitch]
    have h1 : 0 ≤ (D / tau) ^ 2 := sq_nonneg _
    have h2 : 0 < target / Real.log 2 := div_pos htarget0 hlog2
    have h3 : 0 < A / Real.log 2 := div_pos hA0 hlog2
    positivity
  have hAC : A / Real.log 2 < Cswitch := by
    dsimp [Cswitch]
    have h1 : 0 ≤ (D / tau) ^ 2 := sq_nonneg _
    have h2 : 0 < target / Real.log 2 := div_pos htarget0 hlog2
    linarith
  have hCRate : target < Cswitch * Real.log 2 := by
    have hCpart : target / Real.log 2 < Cswitch := by
      dsimp [Cswitch]
      have h1 : 0 ≤ (D / tau) ^ 2 := sq_nonneg _
      have h3 : 0 < A / Real.log 2 := div_pos hA0 hlog2
      linarith
    exact (div_lt_iff₀ hlog2).1 hCpart
  have hcap : D / Real.sqrt Cswitch ≤ tau := by
    have hsqrtC : 0 < Real.sqrt Cswitch := Real.sqrt_pos.2 hC0
    have hsq : (D / tau) ^ 2 < Cswitch := by
      dsimp [Cswitch]
      have h2 : 0 < target / Real.log 2 := div_pos htarget0 hlog2
      have h3 : 0 < A / Real.log 2 := div_pos hA0 hlog2
      linarith
    have hroot : D / tau < Real.sqrt Cswitch := by
      have hleft : 0 ≤ D / tau := (div_pos hD0 htau0).le
      exact (Real.lt_sqrt hleft).2 hsq
    apply (div_le_iff₀ hsqrtC).2
    have hmul := mul_lt_mul_of_pos_left hroot htau0
    have heq : tau * (D / tau) = D := by
      field_simp [ne_of_gt htau0]
    rw [heq] at hmul
    exact hmul.le
  let run : ShrinkingBarrierRunData := {
    rHi := rHi
    rLo := rLo
    rStar := rStar
    tau := tau
    etaLo := etaLo
    D := D
    pHi := pHi
    pLo := pLo
    D_pos := hD0
    tau_lt_a0 := htauA
    etaLo_lt_a0 := hetaLoA
    rStar_eq := rfl
    rStar_pos := hrStar0 }
  have hHigh : kappa <
      min (Cswitch * Real.log 2) (maximalBarrierC0 * D ^ 2) - 5 / 2 := by
    rw [lt_sub_iff_add_lt, lt_min_iff]
    exact ⟨htargetK.trans hCRate, htargetK.trans hDRate⟩
  exact ⟨{
    run := run
    lambdaLo := lambdaLo
    bLo := bLo
    cDyadic := bLo
    Cswitch := Cswitch
    kappa := kappa
    lambdaLo_nonneg := hlambdaLo0
    lambdaLo_lt_one := hlambdaLo1
    bLo_pos := hbLo0
    bLo_lt_rate := by simpa [run] using hbLoRate
    cDyadic_pos := hbLo0
    cDyadic_lt_logTwo := hbLoLog
    Cswitch_pos := hC0
    terminal_below_switch := hAC
    high_cap := by simpa [run] using hcap
    high_rate_margin := by simpa [run] using hHigh
    low_rate_margin := by simpa using hkappa
    clock_pressure := by simpa [run] using hclock
    high_height_contraction := by simpa [run] using hheightContract
    tau_lt_beta := by simpa [run] using htauBeta
    kappa_pos := hkappa0 }⟩
end FirstPassageLinearTransport
