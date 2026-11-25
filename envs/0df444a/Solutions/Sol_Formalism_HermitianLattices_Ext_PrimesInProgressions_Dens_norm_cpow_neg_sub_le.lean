-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_cpow_neg_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:40:30.919085+00:00
-- url     : https://prove2.me/submissions/72a08d33-9b92-4b47-a399-bd95fddbc0bc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(b : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ ≤ ‖w‖ * ((b - a) / a) := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  have ha0 : 0 < a := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]
  have hr : -w - 1 ≠ -1 := by
    intro h; apply hw0; linear_combination -h
  have hint := integral_cpow (a := a) (b := b) (r := -w - 1) (Or.inr ⟨hr, h0⟩)
  have e : -w - 1 + 1 = -w := by ring
  rw [e] at hint
  have hEq : (b : ℂ) ^ (-w) - (a : ℂ) ^ (-w) = -w * ∫ x : ℝ in a..b, (x : ℂ) ^ (-w - 1) := by
    rw [hint]; field_simp
  rw [hEq, norm_mul, norm_neg]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb : ∀ x ∈ Set.uIoc a b, ‖(x : ℂ) ^ (-w - 1)‖ ≤ 1 / a := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hx0 : 0 < x := by linarith
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [hre]
    calc x ^ (-w.re - 1) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 1 / a := by rw [one_div]; exact inv_anti₀ ha0 hx.1.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (by linarith)] at this
  calc _ ≤ 1 / a * (b - a) := this
    _ = (b - a) / a := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
