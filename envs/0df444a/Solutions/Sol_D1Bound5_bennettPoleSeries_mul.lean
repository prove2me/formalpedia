-- Prove2me | solution 1 for D1Bound5.bennettPoleSeries_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:09.624177+00:00
-- url     : https://prove2.me/submissions/b9f35255-6b23-492f-a5ef-46f8184adfc2

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettNegativeBinomial_mul

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







/-- The explicit binomial coefficients really invert the reciprocal pole
factor, rather than merely satisfying a guessed recurrence. -/
theorem _root_.solution (d : F) (hd : d ≠ 0) (k : ℕ) :
    (PowerSeries.C d + PowerSeries.X : PowerSeries F) ^ k * bennettPoleSeries d k = 1 := by
  have hs := congrArg (rescale d⁻¹) (bennettNegativeBinomial_mul (F := F) k)
  simp only [map_mul, map_pow, map_add, map_one, PowerSeries.rescale_X] at hs
  have hf : (PowerSeries.C d + PowerSeries.X : PowerSeries F) =
      PowerSeries.C d * (1 + PowerSeries.C d⁻¹ * PowerSeries.X) := by
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd,
      map_one, one_mul]
  rw [hf, mul_pow, bennettPoleSeries]
  calc
    (PowerSeries.C d) ^ k * (1 + PowerSeries.C d⁻¹ * PowerSeries.X) ^ k *
        (PowerSeries.C ((d⁻¹) ^ k) * rescale d⁻¹ (binomialSeries F (-(k : F)))) =
      PowerSeries.C (d ^ k * (d⁻¹) ^ k) *
        ((1 + PowerSeries.C d⁻¹ * PowerSeries.X) ^ k *
          rescale d⁻¹ (binomialSeries F (-(k : F)))) := by
          simp only [map_mul, map_pow]
          ring
    _ = 1 := by
      rw [hs, ← mul_pow, mul_inv_cancel₀ hd, one_pow, map_one, mul_one]

end D1Bound5
end
