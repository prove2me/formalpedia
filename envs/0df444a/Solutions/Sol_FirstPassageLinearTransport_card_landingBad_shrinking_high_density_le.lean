-- Prove2me | solution 1 for FirstPassageLinearTransport.card_landingBad_shrinking_high_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:40.9578+00:00
-- url     : https://prove2.me/submissions/74d3ed21-63c3-4068-a42b-48176eefff4d

import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_sq_mul
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_landingBad_le_shellBad_add_one
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
import Theorems.Thm_FirstPassageLinearTransport_one_div_two_pow_eq_exp
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lower
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_pos
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
    {M q : ℕ} (hq1 : 1 ≤ q)
    (hHigh : shrinkingSwitchRank C M ≤ q - 1) :
    ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤
      Real.exp (-(Real.log 2 * (q : ℝ))) +
        quadraticWindowShellConstant / 2 *
          Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
            Real.log ((M : ℝ) + 2))) := by
  have hm1 : 1 ≤ q - 1 := by
    have hSpos := shrinkingSwitchRank_pos hC M
    omega
  have hCm : C * Real.log ((M : ℝ) + 2) ≤ ((q - 1 : ℕ) : ℝ) :=
    (shrinkingSwitchRank_lower C M).trans (by exact_mod_cast hHigh)
  have ht0 := shrinkingHighTolerance_pos P M (q - 1)
  have ht1 := (shrinkingHighTolerance_le_tau P M (q - 1)).trans P.pHi.eta_le_one
  have hshell := card_shellInitialWindowBad_le_quadratic
    (M := q - 1) ht0 ht1
  have hexp := shrinkingHighTolerance_sq_mul P hC hcap hm1 hCm
  have hexpScaled :
      maximalBarrierC0 * shrinkingHighTolerance P M (q - 1) ^ 2 *
          (((q - 1 : ℕ) : ℝ)) =
        maximalBarrierC0 * (P.D ^ 2 * Real.log ((M : ℝ) + 2)) := by
    calc
      _ = maximalBarrierC0 *
          (shrinkingHighTolerance P M (q - 1) ^ 2 *
            (((q - 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hexp]
  have hexpScaled' :
      maximalBarrierC0 * shrinkingHighTolerance P M (q - 1) ^ 2 *
          ((q : ℝ) - 1) =
        maximalBarrierC0 * (P.D ^ 2 * Real.log ((M : ℝ) + 2)) := by
    simpa [Nat.cast_sub hq1] using hexpScaled
  have hlandNat := card_landingBad_le_shellBad_add_one hq1
    (shrinkingHighTolerance P M (q - 1))
  have hland :
      ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) ≤
        ((shellInitialWindowBad (q - 1)
          (shrinkingHighTolerance P M (q - 1))).card : ℝ) + 1 := by
    exact_mod_cast hlandNat
  have hpowq : 0 < (2 : ℝ) ^ q := by positivity
  have hpowSub : (2 : ℝ) ^ (q - 1) / (2 : ℝ) ^ q = 1 / 2 := by
    rw [show q = (q - 1) + 1 by omega, pow_succ]
    field_simp
    simp
  calc
    _ ≤ (((shellInitialWindowBad (q - 1)
          (shrinkingHighTolerance P M (q - 1))).card : ℝ) + 1) /
          (2 : ℝ) ^ q := div_le_div_of_nonneg_right hland hpowq.le
    _ ≤ (quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 *
            shrinkingHighTolerance P M (q - 1) ^ 2 * (q - 1))) *
          (2 : ℝ) ^ (q - 1) + 1) / (2 : ℝ) ^ q := by
      apply div_le_div_of_nonneg_right _ hpowq.le
      simpa [Nat.cast_sub hq1] using add_le_add_right hshell 1
    _ = Real.exp (-(Real.log 2 * (q : ℝ))) +
        quadraticWindowShellConstant / 2 *
          Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
            Real.log ((M : ℝ) + 2))) := by
      rw [hexpScaled', add_div, one_div_two_pow_eq_exp]
      have hmain :
          quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 *
                (P.D ^ 2 * Real.log ((M : ℝ) + 2)))) *
              (2 : ℝ) ^ (q - 1) / (2 : ℝ) ^ q =
            quadraticWindowShellConstant / 2 *
              Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := by
        calc
          _ = (quadraticWindowShellConstant *
                Real.exp (-(maximalBarrierC0 *
                  (P.D ^ 2 * Real.log ((M : ℝ) + 2))))) *
                ((2 : ℝ) ^ (q - 1) / (2 : ℝ) ^ q) := by ring
          _ = (quadraticWindowShellConstant *
                Real.exp (-(maximalBarrierC0 *
                  (P.D ^ 2 * Real.log ((M : ℝ) + 2))))) * (1 / 2) := by
            rw [hpowSub]
          _ = _ := by ring
      rw [hmain]
      ring
end FirstPassageLinearTransport
