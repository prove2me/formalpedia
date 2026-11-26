-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_horizon_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:39.638626+00:00
-- url     : https://prove2.me/submissions/05914f7a-1a93-47dd-b25e-f5796d860f27

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_targetScale_pos
import Theorems.Thm_FirstPassageLinearTransport_targetScale_rpow_neg_le
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
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r : ℝ} (hr : 0 < r) :
    ∀ᶠ M : ℕ in Filter.atTop,
      (M : ℝ) / (2 * (targetScale r M : ℝ)) ≤ 1 / 3 := by
  let b := r * Real.log 2
  have hb : 0 < b := mul_pos hr (Real.log_pos (by norm_num))
  have htReal :
      Filter.Tendsto
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-b * x))
        Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  have htNat :
      Filter.Tendsto
        (fun M : ℕ => (M : ℝ) * Real.exp (-b * M))
        Filter.atTop (nhds 0) := by
    simpa [Real.rpow_one, Function.comp_def] using
      htReal.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ M : ℕ in Filter.atTop,
      (M : ℝ) * Real.exp (-b * M) < 1 / 3 :=
    htNat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards [hevent] with M hM
  have hfloor := targetScale_rpow_neg_le hr.le
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
    (M := M)
  have hY : (0 : ℝ) < targetScale r M := by
    exact_mod_cast targetScale_pos r M
  have hrewrite :
      (targetScale r M : ℝ) ^ (-(1 : ℝ)) =
        1 / (targetScale r M : ℝ) := by
    rw [Real.rpow_neg_one]
    simp [one_div]
  rw [hrewrite] at hfloor
  have hcalc :
      (M : ℝ) / (2 * (targetScale r M : ℝ)) ≤
        (M : ℝ) * Real.exp (-(b * M)) := by
    calc
      (M : ℝ) / (2 * (targetScale r M : ℝ)) =
          (M : ℝ) / 2 * (1 / (targetScale r M : ℝ)) := by ring
      _ ≤ (M : ℝ) / 2 *
          (2 * Real.exp (-(r * 1 * M * Real.log 2))) :=
        mul_le_mul_of_nonneg_left hfloor (by positivity)
      _ = (M : ℝ) * Real.exp (-(b * M)) := by
        dsimp [b]
        have hexp :
            -(r * 1 * (M : ℝ) * Real.log 2) =
              -(r * Real.log 2 * (M : ℝ)) := by
          ring
        rw [hexp]
        ring
  have hM' : (M : ℝ) * Real.exp (-(b * M)) ≤ 1 / 3 := by
    simpa only [neg_mul] using hM.le
  exact hcalc.trans hM'
end FirstPassageLinearTransport
