-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.cube_mul_exp_le_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:06.948862+00:00
-- url     : https://prove2.me/submissions/0cd6bfe5-b514-4742-b7a6-46f93d3455e6

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ChebyshevCharacterExplicitGeneral
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExpGainFromZeroFreeRegion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (c₁ s y X : ℝ) (hc₁ : 0 < c₁) (hs0 : 0 < s) (hy0 : 0 < y)
    (hX : X = Real.exp (-(c₁ * s / 2))) :
    s ^ 3 * X * y ≤ 6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s)) := by
  have hu0 : 0 < c₁ * s / 4 := div_pos (mul_pos hc₁ hs0) (by norm_num)
  have hexp : (c₁ * s / 4) ^ 3 / 6 ≤ Real.exp (c₁ * s / 4) := by
    have h := Real.pow_div_factorial_le_exp (c₁ * s / 4) hu0.le 3
    norm_num [Nat.factorial] at h
    linarith
  have hX' : X = Real.exp (-(c₁ * s / 4)) * Real.exp (-(c₁ * s / 4)) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (-(c₁ / 4) * s) = Real.exp (-(c₁ * s / 4)) := by congr 1; ring
  rw [he, hX']
  have hu3 : (c₁ * s / 4) ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 := by
    have h2 : Real.exp (c₁ * s / 4) * Real.exp (-(c₁ * s / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right (by linarith : (c₁ * s / 4) ^ 3 ≤ 6 * Real.exp (c₁ * s / 4))
      (Real.exp_pos (-(c₁ * s / 4))).le
    linarith
  have hsu : s = 8 / (2 * c₁) * (c₁ * s / 4) := by
    have := hc₁.ne'
    field_simp
    try ring
  have hK : 0 ≤ (8 / (2 * c₁)) ^ 3 := pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3
  have key : s ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 * (8 / (2 * c₁)) ^ 3 := by
    have hs3 : s ^ 3 = (8 / (2 * c₁)) ^ 3 * (c₁ * s / 4) ^ 3 := by
      rw [← mul_pow, ← hsu]
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hK]
  nlinarith [mul_le_mul_of_nonneg_right key (mul_pos (Real.exp_pos (-(c₁ * s / 4))) hy0).le]
end Formalism.ZeroFreeDirichlet
