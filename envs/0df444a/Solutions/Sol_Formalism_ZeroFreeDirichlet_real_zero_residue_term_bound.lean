-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.real_zero_residue_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:07.273795+00:00
-- url     : https://prove2.me/submissions/85f1cec3-3b6e-4aca-a0b4-890761c824f6

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (y β σ₁ ε : ℝ) (hy : 1 ≤ y) (hβ : 1 / 2 ≤ β) (hβσ : β ≤ σ₁) (hε : 0 < ε)
    (hgap : ε ≤ 1 - σ₁) :
    ‖(y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (2 / ε) := by
  have hy0 : 0 < y := by linarith
  have hβ1 : β < 1 := by linarith
  have hnum : ‖(y : ℂ) ^ (β : ℂ)‖ = y ^ β := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]; simp
  have hden : ‖(β : ℂ) * ((β : ℂ) - 1)‖ = β * (1 - β) := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_neg (by linarith)]
    ring
  rw [norm_div, hnum, hden]
  have hyb : y ^ β ≤ y ^ σ₁ := Real.rpow_le_rpow_of_exponent_le hy hβσ
  have hd : ε / 2 ≤ β * (1 - β) := by
    nlinarith [mul_le_mul_of_nonneg_right hβ (by linarith : (0:ℝ) ≤ 1 - β)]
  have hyp : 0 < y ^ σ₁ := Real.rpow_pos_of_pos hy0 _
  have h2 : (2 / ε) * (ε / 2) = 1 := by field_simp
  rw [div_le_iff₀ (by linarith)]
  calc y ^ β ≤ y ^ σ₁ := hyb
    _ = y ^ σ₁ * (2 / ε) * (ε / 2) := by rw [mul_assoc _ (2 / ε), h2, mul_one]
    _ ≤ y ^ σ₁ * (2 / ε) * (β * (1 - β)) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hyp.le (by positivity))
end Formalism.ZeroFreeDirichlet
