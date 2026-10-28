-- Prove2me | solution 1 for D1Bound5.bennettBinomial_coefficient_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:02.231113+00:00
-- url     : https://prove2.me/submissions/c9bd9d76-e2f1-4280-80e6-e947a739f3e5

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennettSeries_coeff_C_add_X_pow

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- The one-term binomial identity transferring a coefficient in the residual
variable to a local residue coefficient. It holds for every exponent parameter,
including those shifted to negative values in the node-removal induction. -/
theorem _root_.solution (k h r : ℕ) (hhk : h ≤ k) (ν a : F) :
    Ring.choose ((k : F) + ν) h *
      PowerSeries.coeff r
        (((PowerSeries.X : PowerSeries F) ^ h *
          (1 + PowerSeries.C a * PowerSeries.X) ^ (k - h)) *
            PowerSeries.rescale a (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F) + ν) r *
        PowerSeries.coeff h ((PowerSeries.C a + PowerSeries.X : PowerSeries F) ^ r) := by
  have hseries : (1 + PowerSeries.C a * PowerSeries.X : PowerSeries F) ^ (k - h) *
      PowerSeries.rescale a (PowerSeries.binomialSeries F ν) =
        PowerSeries.rescale a (PowerSeries.binomialSeries F ((k : F) + ν - (h : F))) := by
    calc
      _ = PowerSeries.rescale a
          ((1 + PowerSeries.X : PowerSeries F) ^ (k - h) *
            PowerSeries.binomialSeries F ν) := by
              simp only [map_mul, map_pow, map_add, map_one, PowerSeries.rescale_X]
      _ = _ := by
        congr 1
        rw [← PowerSeries.binomialSeries_nat (R := F), ← PowerSeries.binomialSeries_add]
        congr 1
        rw [Nat.cast_sub hhk]
        ring
  rw [mul_assoc, hseries, PowerSeries.coeff_X_pow_mul', bennettSeries_coeff_C_add_X_pow]
  by_cases hhr : h ≤ r
  · rw [if_pos hhr, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff]
    simp only [smul_eq_mul, mul_one]
    have hchoose := Ring.choose_smul_choose ((k : F) + ν) hhr
    simp only [nsmul_eq_mul] at hchoose
    calc
      Ring.choose ((k : F) + ν) h *
          (a ^ (r - h) * Ring.choose ((k : F) + ν - (h : F)) (r - h)) =
          (Ring.choose ((k : F) + ν) h *
            Ring.choose ((k : F) + ν - (h : F)) (r - h)) * a ^ (r - h) := by ring
      _ = _ := by rw [← hchoose]; ring
  · rw [if_neg hhr, Nat.choose_eq_zero_of_lt (lt_of_not_ge hhr)]
    simp

end D1Bound5
end
