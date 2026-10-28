-- Prove2me | solution 1 for D1Bound5.bennett_two_row_radius_power_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:52.62862+00:00
-- url     : https://prove2.me/submissions/3494a81f-b82b-48e4-8c49-25a64d23973a

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5



/-- The one extra pole in a residue row always pays for the coefficient
radius. This is the algebraic counterpart of cancellation of circle length
with the extra pole in the contour proof. -/
theorem _root_.solution
    (r D E : ℝ) (hr : 0 < r) (hD : r ≤ D) (hE : r ≤ E)
    (k d0 d1 d2 : ℕ) (hk : 1 ≤ k) (hd : d0 + d1 + d2 = 1) :
    (r * D * E) ^ k ≤ r ^ (k + d0 - 1) * D ^ (k + d1) * E ^ (k + d2) := by
  have hD0 : 0 ≤ D := hr.le.trans hD
  have hE0 : 0 ≤ E := hr.le.trans hE
  have hextra : r ≤ r ^ d0 * D ^ d1 * E ^ d2 := by
    calc
      r = r ^ (d0 + d1 + d2) := by rw [hd, pow_one]
      _ = r ^ d0 * r ^ d1 * r ^ d2 := by rw [pow_add, pow_add]
      _ ≤ r ^ d0 * D ^ d1 * E ^ d2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hD d1) (pow_nonneg hr.le _))
          (pow_le_pow_left₀ hr.le hE d2) (pow_nonneg hr.le _)
          (mul_nonneg (pow_nonneg hr.le _) (pow_nonneg hD0 _))
  have ht : (k + d0 - 1) + 1 = k + d0 := by omega
  apply (mul_le_mul_iff_of_pos_right hr).mp
  calc
    (r * D * E) ^ k * r ≤ (r * D * E) ^ k *
        (r ^ d0 * D ^ d1 * E ^ d2) :=
      mul_le_mul_of_nonneg_left hextra
        (pow_nonneg (mul_nonneg (mul_nonneg hr.le hD0) hE0) _)
    _ = (r ^ (k + d0 - 1) * D ^ (k + d1) * E ^ (k + d2)) * r := by
      have hrpow : r ^ (k + d0 - 1) * r = r ^ k * r ^ d0 := by
        rw [← pow_succ, ht, pow_add]
      rw [pow_add, pow_add]
      simp only [mul_pow]
      calc
        _ = (r ^ k * r ^ d0) * (D ^ k * D ^ d1) * (E ^ k * E ^ d2) := by ring
        _ = _ := by rw [← hrpow]; ring







end D1Bound5
end
