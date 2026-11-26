-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_shrinkingPolylogTerminalProfile_le_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:53.452788+00:00
-- url     : https://prove2.me/submissions/f94251bc-e94f-42d8-a485-4455b0390ac6

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_eventually_sqrtSupport_mul_terminalTail_polylog_le_power
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighDensityProfile_le_rpow
import Theorems.Thm_FirstPassageLinearTransport_eventually_sqrtSupport_mul_quadratic_rpow_le_power
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
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
import Theorems.Thm_FirstPassageLinearTransport_quadraticWindowShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingTimeSupportConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_terminalTailPrefactor_pos
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
    (P : ShrinkingBarrierRunData)
    {A C b b' c' kappa : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (hHigh : kappa <
      min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2) - 5 / 2)
    (hLow : kappa < A * min b' c' / Real.log 2 - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      let dHi := shrinkingHighDensityProfile P C M
      let H := (shrinkingTimeSupportConstant P C + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      dHi + H * (1 + 6 / (P.rStar : ℝ)) *
          (((M : ℝ) + 1) ^ 2 * dHi +
            terminalTailBound b b' c' (polylogTerminalRank A M)) ≤
        shrinkingPolylogProfileConstant P C b b' c' *
          (((M : ℝ) + 2) ^ (-kappa)) := by
  let pHi := min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2)
  let K := 1 + quadraticWindowShellConstant
  let T := shrinkingTimeSupportConstant P C + 1
  let R := 1 + 6 / (P.rStar : ℝ)
  let pref := terminalTailPrefactor b b' c'
  have hHighBase := eventually_sqrtSupport_mul_quadratic_rpow_le_power
    (p := pHi) (kappa := kappa) (by simpa [pHi] using hHigh)
  have hLowBase := eventually_sqrtSupport_mul_terminalTail_polylog_le_power
    hA hb' hbb' hc' hc2 hLow
  filter_upwards [hHighBase, hLowBase] with M hHighBase hLowBase
  let x : ℝ := (M : ℝ) + 2
  let dHi := shrinkingHighDensityProfile P C M
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have := quadraticWindowShellConstant_pos
    positivity
  have hT0 : 0 ≤ T := by
    dsimp [T]
    linarith [shrinkingTimeSupportConstant_pos P hC]
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have hr : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
    positivity
  have hpref0 : 0 ≤ pref := by
    dsimp [pref]
    exact (terminalTailPrefactor_pos hb' hbb' hc' hc2).le
  have hdHi : dHi ≤ K * x ^ (-pHi) := by
    simpa [dHi, K, x, pHi] using shrinkingHighDensityProfile_le_rpow P C M
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad : 0 ≤ quadraticWindowShellConstant :=
      quadraticWindowShellConstant_pos.le
    positivity
  have hDirectPower : x ^ (-pHi) ≤ x ^ (-kappa) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by
      dsimp [pHi] at hHigh ⊢
      linarith)
  have hDirect : dHi ≤ K * x ^ (-kappa) :=
    hdHi.trans (mul_le_mul_of_nonneg_left hDirectPower hK0)
  have hHighTerm :
      T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * dHi) ≤
        (T * R * K) * x ^ (-kappa) := by
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * (K * x ^ (-pHi))) := by
        gcongr
      _ = T * R * K *
          (Real.sqrt (x * Real.log x) *
            (((M : ℝ) + 1) ^ 2 * x ^ (-pHi))) := by ring
      _ ≤ (T * R * K) * x ^ (-kappa) := by
        exact mul_le_mul_of_nonneg_left (by simpa [x, pHi] using hHighBase)
          (mul_nonneg (mul_nonneg hT0 hR0) hK0)
  have hLowTerm :
      T * Real.sqrt (x * Real.log x) * R *
          terminalTailBound b b' c' (polylogTerminalRank A M) ≤
        (T * R * pref) * x ^ (-kappa) := by
    calc
      _ = T * R *
          (Real.sqrt (x * Real.log x) *
            terminalTailBound b b' c' (polylogTerminalRank A M)) := by ring
      _ ≤ (T * R) * (pref * x ^ (-kappa)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [x, pref] using hLowBase)
          (mul_nonneg hT0 hR0)
      _ = (T * R * pref) * x ^ (-kappa) := by ring
  dsimp only
  calc
    dHi + T * Real.sqrt (x * Real.log x) * R *
        (((M : ℝ) + 1) ^ 2 * dHi +
          terminalTailBound b b' c' (polylogTerminalRank A M)) =
      dHi +
        T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * dHi) +
        T * Real.sqrt (x * Real.log x) * R *
          terminalTailBound b b' c' (polylogTerminalRank A M) := by ring
    _ ≤ K * x ^ (-kappa) +
        (T * R * K) * x ^ (-kappa) +
        (T * R * pref) * x ^ (-kappa) :=
      add_le_add (add_le_add hDirect hHighTerm) hLowTerm
    _ = shrinkingPolylogProfileConstant P C b b' c' *
        (((M : ℝ) + 2) ^ (-kappa)) := by
      unfold shrinkingPolylogProfileConstant
      dsimp [K, T, R, pref, x]
      ring
end FirstPassageLinearTransport
