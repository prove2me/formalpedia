-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.norm_cpow_sub_le_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:27.017872+00:00
-- url     : https://prove2.me/submissions/39777df3-08b1-4f48-887d-a19c91dfcd7f

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Theorems.Thm_P2M_Formalism_ZF_ComplexPowerDifferenceIntegral_cpow_sub_eq_integral__4fc9b530b8b0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxa : x ≤ a + 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hxpos : 0 < x := lt_of_lt_of_le ha hax
  rw [cpow_sub_eq_integral' hxpos hxa hs0, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hC : ∀ t ∈ Set.uIoc x (a + 1), ‖(t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) := by
    intro t ht
    rw [Set.uIoc_of_le hxa] at ht
    have hta : a ≤ t := le_trans hax ht.1.le
    have ht0 : 0 < t := lt_of_lt_of_le ha hta
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos ha hta (by linarith)
  calc ‖∫ t in x..(a + 1), (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) * |a + 1 - x| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ ≤ a ^ (-s.re - 1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha.le _)
        rw [abs_of_nonneg (by linarith)]; linarith
    _ = a ^ (-s.re - 1) := mul_one _
end Formalism.ZF.ComplexPowerDifferenceIntegral
