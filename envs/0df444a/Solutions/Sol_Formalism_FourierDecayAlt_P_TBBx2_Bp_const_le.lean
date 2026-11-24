-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Bp.const_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:11.969096+00:00
-- url     : https://prove2.me/submissions/2792e62c-2828-4f54-b359-1fd3f055adc8

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_expo_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Bp_constant_le_rpow_of_three_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Bp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.TBBx2.Bp
theorem _root_.solution (C₃ CΛ C₀ C₂ Cκ b Λ κ₀ : ℝ) (r n₀ p₀ : ℕ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hC₂ : 0 < C₂) (hb : 3 ≤ b) (hΛ : 1 ≤ Λ) (hΛb : Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)))
    (hκ : 0 < κ₀) (hκb : κ₀ ≤ b ^ (Cκ * ((2 * r + 2 : ℕ) : ℝ) ^ 2))
    (hn₀ : n₀ ≤ 30 * (r + 1) ^ 2 + 6) (hp₀ : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) *
        b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤
      b ^ ((40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10)) *
        ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hc0 : (0 : ℝ) ≤ max 0 (Real.log C₂ / Real.log 3) := le_max_left _ _
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have f1 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have f2 : (3 * b) ^ (2 * n₀) ≤ b ^ ((4 * n₀ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    calc (3 * b) ^ (2 * n₀) ≤ (b * b) ^ (2 * n₀) :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) _
      _ = b ^ (4 * n₀) := by ring
  have f3 : κ₀ ≤ b ^ (|Cκ| * ((2 * r + 2 : ℕ) : ℝ) ^ 2) :=
    hκb.trans (Real.rpow_le_rpow_of_exponent_le hb1
      (mul_le_mul_of_nonneg_right (le_abs_self Cκ) (sq_nonneg _)))
  have f4 : C₂ * Λ ^ 2 ≤ b ^ (max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) := by
    rw [Real.rpow_add hb0]
    refine mul_le_mul (constant_le_rpow_of_three_le C₂ b hC₂ hb) ?_ (sq_nonneg _) (by positivity)
    calc Λ ^ 2 ≤ (b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 := pow_le_pow_left₀ hΛ0 hΛb 2
      _ = b ^ (2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) := by
        rw [← Real.rpow_mul_natCast hb0.le]
        congr 1
        push_cast
        ring
  have f5 : (C₂ * Λ ^ 2) ^ (r + 1) ≤ b ^ ((max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact pow_le_pow_left₀ (mul_nonneg hC₂.le (sq_nonneg _)) f4 _
  have hE := expo_le C₃ CΛ C₀ (max 0 (Real.log C₂ / Real.log 3)) |Cκ| r n₀ p₀ hC₃ hCΛ hC₀ hc0 (abs_nonneg _) hn₀ hp₀
  calc 2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) * b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))
      ≤ b ^ (1 : ℝ) * b ^ ((4 * n₀ : ℕ) : ℝ) *
          (b ^ (|Cκ| * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * b ^ ((max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ))) *
          b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul f1 f2 (by positivity) (by positivity))
            (mul_le_mul f3 f5 (by positivity) (by positivity)) (by positivity) (by positivity))
          (by positivity)
    _ = b ^ (1 + ((4 * n₀ : ℕ) : ℝ) + |Cκ| * ((2 * r + 2 : ℕ) : ℝ) ^ 2 +
          (max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ) + 2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 hE
end Formalism.FourierDecayAlt.P.TBBx2.Bp
