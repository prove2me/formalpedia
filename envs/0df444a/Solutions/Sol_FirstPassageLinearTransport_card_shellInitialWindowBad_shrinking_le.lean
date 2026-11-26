-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellInitialWindowBad_shrinking_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:08.836134+00:00
-- url     : https://prove2.me/submissions/c3392f2d-2b19-4f47-bf20-cc7d32167ff1

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_eq_formula
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_sq_mul
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_le_quadratic
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
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lower
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
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



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M ≤ M) :
    ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
          Real.log ((M : ℝ) + 2))) := by
  have hCM : C * Real.log ((M : ℝ) + 2) ≤ (M : ℝ) :=
    (shrinkingSwitchRank_lower C M).trans (by exact_mod_cast hSwitch)
  have htEq := shrinkingHighTolerance_eq_formula P hC hcap hM hCM
  have ht0 := shrinkingHighTolerance_pos P M M
  have ht1 := (shrinkingHighTolerance_le_tau P M M).trans P.pHi.eta_le_one
  have hcard := card_shellInitialWindowBad_le_quadratic
    (M := M) ht0 ht1
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  have hdiv := (div_le_iff₀ hpow).2 hcard
  have hexp := shrinkingHighTolerance_sq_mul P hC hcap hM hCM
  have hexpScaled :
      maximalBarrierC0 * shrinkingHighTolerance P M M ^ 2 * (M : ℝ) =
        maximalBarrierC0 * (P.D ^ 2 * Real.log ((M : ℝ) + 2)) := by
    calc
      _ = maximalBarrierC0 *
          (shrinkingHighTolerance P M M ^ 2 * (M : ℝ)) := by ring
      _ = _ := by rw [hexp]
  calc
    _ ≤ quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 *
            shrinkingHighTolerance P M M ^ 2 * M)) := by
      simpa [mul_assoc] using hdiv
    _ = quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
          Real.log ((M : ℝ) + 2))) := by
      rw [hexpScaled]
      ring
end FirstPassageLinearTransport
