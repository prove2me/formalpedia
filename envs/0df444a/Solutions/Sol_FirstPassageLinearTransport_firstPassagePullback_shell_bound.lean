-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassagePullback_shell_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:15.579833+00:00
-- url     : https://prove2.me/submissions/2ab20dd8-587b-4e0c-94e0-b40fb2114c42

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_card_shellBad_pullback_le
import Theorems.Thm_FirstPassageLinearTransport_transportedBad_le_paid
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_shellBad_le
import Theorems.Thm_FirstPassageLinearTransport_pullbackShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
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



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta C D chi Dc : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi0 : 0 < chi) (hchi : chi < r)
    (hDc0 : 0 < Dc)
    (hDDc : D ≤ Dc)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (M : ℕ) :
    ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
      pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
  classical
  have hD0 := hS.D_pos
  have hD1 := hS.D_le_one
  have hC0 := hS.C_pos
  have hC1 : 1 ≤ C + 1 := by linarith
  have hDinv : 1 ≤ D⁻¹ ^ 2 := by
    have hInv : 1 ≤ D⁻¹ := by
      exact (one_le_inv₀ hD0).2 hD1
    exact one_le_pow₀ hInv
  by_cases hlarge : p.M0 ≤ M
  · have hcardNat := card_shellBad_pullback_le p S hlarge
    have hcard :
        ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
          ((shellBad (extendedWindow p) M).card : ℝ) +
            ((transportedSources M (targetScale r M) M
              (badTarget S (targetScale r M))).card : ℝ) := by
      exact_mod_cast hcardNat
    have hW := extendedWindow_shellBad_le p hDDc hchi0.le hDcRate M
    have hT := transportedBad_le_paid p S hS hchi hlarge
    have hcoeff :
        2 * quadraticWindowGlobalConstant eta +
            (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 ≤
          pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
      have hWconst := (extendedWindow_powerDense p).C_pos.le
      have hgap : 0 ≤ 20 / transportGap r chi ^ 2 := by positivity
      have hstart : 0 ≤ Real.exp (chi * Dc * Real.log 2 * p.M0) := by
        positivity
      have hB : 0 ≤ 2 * quadraticWindowGlobalConstant eta := by positivity
      have hE : 0 ≤ D⁻¹ ^ 2 := sq_nonneg _
      have hCplus : 0 ≤ C + 1 := (by linarith : 0 ≤ C + 1)
      have hF : 1 ≤ (C + 1) * D⁻¹ ^ 2 := by
        simpa only [one_mul] using
          mul_le_mul hC1 hDinv (by norm_num : (0 : ℝ) ≤ 1) hCplus
      have hBpay :
          2 * quadraticWindowGlobalConstant eta ≤
            (2 * quadraticWindowGlobalConstant eta) * ((C + 1) * D⁻¹ ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hF hB
      have hGpay :
          (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 ≤
            (20 / transportGap r chi ^ 2) * (C + 1) * D⁻¹ ^ 2 := by
        have hCle : C ≤ C + 1 := by linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCle hgap) hE
      calc
        2 * quadraticWindowGlobalConstant eta +
              (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 ≤
            (2 * quadraticWindowGlobalConstant eta) * ((C + 1) * D⁻¹ ^ 2) +
              (20 / transportGap r chi ^ 2) * (C + 1) * D⁻¹ ^ 2 :=
          add_le_add hBpay hGpay
        _ = (2 * quadraticWindowGlobalConstant eta +
              20 / transportGap r chi ^ 2) * ((C + 1) * D⁻¹ ^ 2) := by ring
        _ ≤ (Real.exp (chi * Dc * Real.log 2 * p.M0) +
              2 * quadraticWindowGlobalConstant eta +
              20 / transportGap r chi ^ 2) * ((C + 1) * D⁻¹ ^ 2) := by
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hCplus hE)
        _ = pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
          unfold pullbackShellConstant
          ring
    have hnonneg :
        0 ≤ Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
      positivity
    calc
      _ ≤ ((shellBad (extendedWindow p) M).card : ℝ) +
          ((transportedSources M (targetScale r M) M
            (badTarget S (targetScale r M))).card : ℝ) := hcard
      _ ≤ (2 * quadraticWindowGlobalConstant eta +
            (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2) *
          Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
        nlinarith [hW, hT]
      _ ≤ pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
          Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
        calc
          _ = (2 * quadraticWindowGlobalConstant eta +
                (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2) *
              (Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M) := by
            ring
          _ ≤ (pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2) *
              (Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M) :=
            mul_le_mul_of_nonneg_right hcoeff hnonneg
          _ = _ := by ring
  · have hMlt : M < p.M0 := by omega
    have hcardNat :
        (shellBad (firstPassagePullback p S) M).card ≤ (dyadicShell M).card := by
      apply Finset.card_le_card
      intro n hn
      exact (Finset.mem_filter.mp hn).1
    have hcard :
        ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
          (2 : ℝ) ^ M := by
      rw [card_dyadicShell] at hcardNat
      exact_mod_cast hcardNat
    have hrate :
        chi * D * (M : ℝ) ≤ chi * Dc * p.M0 := by
      have hMle : (M : ℝ) ≤ p.M0 := by exact_mod_cast hMlt.le
      calc
        chi * D * (M : ℝ) ≤ chi * Dc * (M : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDDc hchi0.le) (Nat.cast_nonneg M)
        _ ≤ chi * Dc * (p.M0 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hMle
            (mul_nonneg hchi0.le hDc0.le)
    have hfactor :
        1 ≤ Real.exp (chi * Dc * Real.log 2 * p.M0) *
          Real.exp (-(chi * D * Real.log 2 * M)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    have hK :
        Real.exp (chi * Dc * Real.log 2 * p.M0) ≤
          pullbackShellConstant p chi Dc := by
      unfold pullbackShellConstant
      have hWconst := (extendedWindow_powerDense p).C_pos.le
      have hgap : 0 ≤ 20 / transportGap r chi ^ 2 := by positivity
      nlinarith
    have hbig :
        1 ≤ pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
          Real.exp (-(chi * D * Real.log 2 * M)) := by
      have hKC :
          Real.exp (chi * Dc * Real.log 2 * p.M0) ≤
            pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
        calc
          _ ≤ pullbackShellConstant p chi Dc := hK
          _ ≤ pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
            have hpK := (pullbackShellConstant_pos (Dc := Dc) p hchi).le
            have hCplus : 0 ≤ C + 1 := by linarith
            have hF : 1 ≤ (C + 1) * D⁻¹ ^ 2 := by
              simpa only [one_mul] using
                mul_le_mul hC1 hDinv (by norm_num : (0 : ℝ) ≤ 1) hCplus
            calc
              pullbackShellConstant p chi Dc =
                  pullbackShellConstant p chi Dc * 1 := by ring
              _ ≤ pullbackShellConstant p chi Dc * ((C + 1) * D⁻¹ ^ 2) :=
                mul_le_mul_of_nonneg_left hF hpK
              _ = pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
                ring
      have hexp0 : 0 ≤ Real.exp (-(chi * D * Real.log 2 * M)) := by
        positivity
      exact hfactor.trans
        (mul_le_mul_of_nonneg_right hKC hexp0)
    calc
      _ ≤ (2 : ℝ) ^ M := hcard
      _ = 1 * (2 : ℝ) ^ M := by ring
      _ ≤ (pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
          Real.exp (-(chi * D * Real.log 2 * M))) * (2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = _ := by ring
end FirstPassageLinearTransport
