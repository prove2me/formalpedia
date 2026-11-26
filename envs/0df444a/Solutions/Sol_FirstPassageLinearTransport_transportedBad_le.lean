-- Prove2me | solution 1 for FirstPassageLinearTransport.transportedBad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:35.905445+00:00
-- url     : https://prove2.me/submissions/85fa36b4-528b-422d-b172-08b22d2d956b

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_card_badTarget
import Theorems.Thm_FirstPassageLinearTransport_targetScale_pos
import Theorems.Thm_FirstPassageLinearTransport_targetScale_rpow_neg_le
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound
import Theorems.Thm_FirstPassageLinearTransport_arbitraryTarget_linear_transport
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
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
theorem _root_.solution {r eta C D : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    {M : ℕ} (hM : p.M0 ≤ M) :
    ((transportedSources M (targetScale r M) M
      (badTarget S (targetScale r M))).card : ℝ) ≤
      5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        Real.exp (-(r * D * M * Real.log 2)) := by
  let Y := targetScale r M
  have hY : 0 < Y := targetScale_pos r M
  have hYone : 1 ≤ Y := hY
  have hYM := p.target_lt_shell M hM
  have hMpos : 1 ≤ M := by
    have hYgt := p.target_one_lt M hM
    by_contra hzero
    have : M = 0 := by omega
    subst M
    have hbad := p.target_one_lt 0 hM
    norm_num [targetScale] at hbad
  have htransportQ := arbitraryTarget_linear_transport
    (M := M) (Y := Y) (H := M) (badTarget S Y)
    hY hMpos (p.horizon_small M hM) hYM
  have htransport :
      ((transportedSources M Y M (badTarget S Y)).card : ℝ) ≤
        (5 / 2 : ℝ) * (M : ℝ) ^ 2 * (2 : ℝ) ^ M /
          (Y : ℝ) * ((badTarget S Y).card : ℝ) := by
    have hcast :
        (((transportedSources M Y M (badTarget S Y)).card : ℚ) : ℝ) ≤
          (((5 / 2 : ℚ) * (M : ℚ) ^ 2 * (2 : ℚ) ^ M /
            (Y : ℚ) * ((badTarget S Y).card : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.2 htransportQ
    simpa using hcast
  have hbad : ((badTarget S Y).card : ℝ) ≤
      C * (Y : ℝ) ^ (1 - D) := by
    rw [card_badTarget]
    exact hS.bad_bound Y hYone
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hC : 0 < C := hS.C_pos
  have hmain :
      ((transportedSources M Y M (badTarget S Y)).card : ℝ) ≤
        (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
          (Y : ℝ) ^ (-D) := by
    calc
      _ ≤ (5 / 2 : ℝ) * (M : ℝ) ^ 2 * (2 : ℝ) ^ M /
          (Y : ℝ) * ((badTarget S Y).card : ℝ) := htransport
      _ ≤ (5 / 2 : ℝ) * (M : ℝ) ^ 2 * (2 : ℝ) ^ M /
          (Y : ℝ) * (C * (Y : ℝ) ^ (1 - D)) := by
        exact mul_le_mul_of_nonneg_left hbad (by positivity)
      _ = (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
          (Y : ℝ) ^ (-D) := by
        rw [show (1 : ℝ) - D = 1 + (-D) by ring,
          Real.rpow_add hYreal, Real.rpow_one]
        field_simp
  have hfloor := targetScale_rpow_neg_le p.r_pos.le hS.D_pos.le hS.D_le_one
    (M := M)
  calc
    _ ≤ (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        (Y : ℝ) ^ (-D) := hmain
    _ ≤ (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        (2 * Real.exp (-(r * D * M * Real.log 2))) := by
      exact mul_le_mul_of_nonneg_left hfloor (by positivity)
    _ = 5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        Real.exp (-(r * D * M * Real.log 2)) := by ring
end FirstPassageLinearTransport
