-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_error_terms_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:22.195556+00:00
-- url     : https://prove2.me/submissions/4795bc1f-c08f-4144-a00b-42f108b34e45

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
theorem _root_.solution (C C₀ c₁ y T X L Pw Y ℓ : ℝ) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hy0 : 0 < y) (hT1 : 1 ≤ T) (hTX : T * X = 1) (hL0 : 0 ≤ L) (hY : 0 ≤ Y)
    (hℓP : ℓ ≤ Pw) (hP1 : 1 ≤ Pw) (hL2P : L ^ 2 ≤ Pw) (hL3P : L ^ 3 ≤ Pw) (hLP : L ≤ Pw) :
    2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T)
        + Y * (8 * L / c₁) ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
        16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁) * Pw * (y * X + T * Y) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by nlinarith
  have hX1 : X ≤ 1 := by nlinarith
  have e1 : ∀ z : ℝ, z / T = z * X := fun z => by
    rw [div_eq_iff hT0.ne', mul_assoc, mul_comm X T, hTX, mul_one]
  have e2 : ∀ z : ℝ, z / T ^ 2 = z * X * X := fun z => by
    rw [div_eq_iff (pow_pos hT0 2).ne']
    calc z = z * (T * X) * (T * X) := by rw [hTX]; ring
      _ = z * X * X * T ^ 2 := by ring
  simp only [e1, e2]
  have hPw : 0 ≤ Pw := by linarith
  have hyX : 0 ≤ y * X := mul_nonneg hy0.le hX0.le
  have hTY : 0 ≤ T * Y := mul_nonneg hT0.le hY
  have hcC : 0 ≤ C / c₁ := div_nonneg hC hc₁.le
  have hc2 : 0 ≤ 24 / c₁ ^ 2 := by positivity
  have h8 : 0 ≤ 8 / c₁ := div_nonneg (by norm_num) hc₁.le
  have k1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
  have k2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
  have k3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) := mul_nonneg (by norm_num) (add_nonneg hcC hc2)
  have h1 : 2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) * X ≤
      2 * Real.pi * Real.exp 1 * (1 + C₀) * Pw * (y * X) := by
    have hA : ℓ + C₀ ≤ (1 + C₀) * Pw := by nlinarith
    have hk : 0 ≤ 2 * Real.pi * Real.exp 1 * (y * X) := mul_nonneg (by positivity) hyX
    have := mul_le_mul_of_nonneg_left hA hk
    linarith
  have hB0 : 0 ≤ C * L ^ 2 + 1 := add_nonneg (mul_nonneg hC (sq_nonneg L)) zero_le_one
  have hB : C * L ^ 2 + 1 ≤ (C + 1) * Pw := by
    linarith [mul_le_mul_of_nonneg_left hL2P hC]
  have hXX : X * X ≤ X := mul_le_of_le_one_right hX0.le hX1
  have h2 : (C * L ^ 2 + 1) * (Real.exp 1 * y) * X * X * 3 ≤ 3 * Real.exp 1 * (C + 1) * Pw * (y * X) := by
    have s1 : (C * L ^ 2 + 1) * (X * X) ≤ (C * L ^ 2 + 1) * X := mul_le_mul_of_nonneg_left hXX hB0
    have s2 : (C * L ^ 2 + 1) * X ≤ (C + 1) * Pw * X := mul_le_mul_of_nonneg_right hB hX0.le
    have s3 := mul_le_mul_of_nonneg_left (s1.trans s2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (mul_nonneg (Real.exp_pos 1).le hy0.le))
    linarith
  have h3 : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) ≤
      16 * (C / c₁ + 24 / c₁ ^ 2) * Pw * (T * Y) := by
    have hid : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) =
        (16 * (C / c₁) * L ^ 3 + 16 * (24 / c₁ ^ 2) * L ^ 2) * (T * Y) := by ring
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ hTY
    linarith [mul_le_mul_of_nonneg_left hL3P hcC, mul_le_mul_of_nonneg_left hL2P hc2]
  have h4 : Y * (8 * L / c₁) ≤ 8 / c₁ * Pw * (T * Y) := by
    have hid : Y * (8 * L / c₁) = 8 / c₁ * L * Y := by ring
    rw [hid]
    have s1 : 8 / c₁ * L ≤ 8 / c₁ * Pw := mul_le_mul_of_nonneg_left hLP h8
    have s2 : Y ≤ T * Y := by nlinarith
    calc 8 / c₁ * L * Y ≤ 8 / c₁ * Pw * Y := mul_le_mul_of_nonneg_right s1 hY
      _ ≤ 8 / c₁ * Pw * (T * Y) := mul_le_mul_of_nonneg_left s2 (mul_nonneg h8 hPw)
  nlinarith [mul_nonneg (mul_nonneg k1 hPw) hTY, mul_nonneg (mul_nonneg k2 hPw) hTY,
    mul_nonneg (mul_nonneg k3 hPw) hyX, mul_nonneg (mul_nonneg h8 hPw) hyX]
end Formalism.ZeroFreeDirichlet
