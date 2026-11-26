-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapC_terminal_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:08.056259+00:00
-- url     : https://prove2.me/submissions/3e2ab018-7cb2-4622-b966-f28bbb070384

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_pos
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_le_Dc
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_pos
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_terminal_le
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_pullbackShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1) (hchiDc : chi * Dc < 1)
    (R : ℕ) :
    bootstrapC p chi Dc R + 2 ≤
      (quadraticWindowGlobalConstant eta + 2) *
        (bootstrapStageK p chi Dc *
          (bootstrapD chi Dc R)⁻¹ ^ 2) ^ R := by
  let F := bootstrapStageK p chi Dc * (bootstrapD chi Dc R)⁻¹ ^ 2
  have hK0 : 0 < pullbackGlobalConstant p chi Dc := by
    have hnum : 0 < 2 * pullbackShellConstant p chi Dc :=
      mul_pos (by norm_num) (pullbackShellConstant_pos p hchir)
    have hden : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlt : -Real.log 2 < -(chi * Dc * Real.log 2) := by
        nlinarith
      have hexp := Real.exp_lt_exp.2 hlt
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
      nlinarith
    simpa [pullbackGlobalConstant] using div_pos hnum hden
  have hstage1 : 1 ≤ bootstrapStageK p chi Dc := by
    unfold bootstrapStageK
    linarith
  have hDR0 := bootstrapD_pos hchi0 hDc0 R
  have hDR1 : bootstrapD chi Dc R ≤ 1 :=
    (bootstrapD_le_Dc hchi0.le hchi1 hDc0.le R).trans hDc1
  have hinv1 : 1 ≤ (bootstrapD chi Dc R)⁻¹ :=
    (one_le_inv₀ hDR0).2 hDR1
  have hinvSq : 1 ≤ (bootstrapD chi Dc R)⁻¹ ^ 2 :=
    one_le_pow₀ hinv1
  have hF1 : 1 ≤ F := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le hstage1 hinvSq
  have hF0 : 0 ≤ F := zero_le_one.trans hF1
  have hbaseC : 0 < quadraticWindowGlobalConstant eta :=
    (extendedWindow_powerDense p).C_pos
  have hind : ∀ j : ℕ, j ≤ R →
      bootstrapC p chi Dc j + 2 ≤
        (quadraticWindowGlobalConstant eta + 2) * F ^ j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hjR : j ≤ R := by omega
        have hprev := ih hjR
        have hDj0 := bootstrapD_pos hchi0 hDc0 j
        have hterm := bootstrapD_terminal_le hchi0.le hchi1 hDc0.le hjR
        have hinv :
            (bootstrapD chi Dc j)⁻¹ ≤ (bootstrapD chi Dc R)⁻¹ :=
          (inv_le_inv₀ hDj0 hDR0).2 hterm
        have hinvSq' :
            (bootstrapD chi Dc j)⁻¹ ^ 2 ≤
              (bootstrapD chi Dc R)⁻¹ ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.mpr hDj0.le) hinv 2
        have hCj := bootstrapC_pos p hchi0 hchir hDc0 hchiDc j
        have hrec :
            bootstrapC p chi Dc (j + 1) + 2 ≤
              F * (bootstrapC p chi Dc j + 2) := by
          rw [bootstrapC_succ]
          have hC12 : bootstrapC p chi Dc j + 1 ≤
              bootstrapC p chi Dc j + 2 := by linarith
          have hprod :
              (bootstrapC p chi Dc j + 1) *
                    (bootstrapD chi Dc j)⁻¹ ^ 2 ≤
                (bootstrapC p chi Dc j + 2) *
                    (bootstrapD chi Dc R)⁻¹ ^ 2 :=
            mul_le_mul hC12 hinvSq' (by positivity) (by linarith)
          have htail :
              2 ≤ 2 * ((bootstrapD chi Dc R)⁻¹ ^ 2 *
                (bootstrapC p chi Dc j + 2)) := by
            have hcommon : 1 ≤ (bootstrapD chi Dc R)⁻¹ ^ 2 *
                (bootstrapC p chi Dc j + 2) :=
              one_le_mul_of_one_le_of_one_le hinvSq (by linarith)
            nlinarith
          dsimp [F]
          unfold bootstrapStageK
          have hfirst := mul_le_mul_of_nonneg_left hprod hK0.le
          nlinarith
        calc
          bootstrapC p chi Dc (j + 1) + 2 ≤
              F * (bootstrapC p chi Dc j + 2) := hrec
          _ ≤ F * ((quadraticWindowGlobalConstant eta + 2) * F ^ j) :=
            mul_le_mul_of_nonneg_left hprev hF0
          _ = (quadraticWindowGlobalConstant eta + 2) * F ^ (j + 1) := by
            rw [pow_succ]
            ring
  simpa [F] using hind R le_rfl
end FirstPassageLinearTransport
