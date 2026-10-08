-- Prove2me | solution 1 for Conway99Formal.TwoSidedSchur.reciprocal_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:12:14.415988+00:00
-- url     : https://prove2.me/submissions/91b1e636-4f7e-4e57-bed1-f1d37270308f

import Mathlib

namespace Conway99Formal.TwoSidedSchur
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

namespace Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

















end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

open Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

open Conway99Formal.TwoSidedSchur in
theorem solution (a : ℝ) (ha : 0 < a) (hb : a < 28) :
    1 / 7 ≤ 1 / a + 1 / (28 - a) := by
  have hba : 0 < 28 - a := by linarith
  have hprod : 0 < a * (28 - a) := mul_pos ha hba
  have hsq : 0 ≤ (a - 14) ^ 2 := sq_nonneg _
  calc
    1 / 7 ≤ 28 / (a * (28 - a)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) hprod).2
      nlinarith
    _ = 1 / a + 1 / (28 - a) := by
      field_simp
      ring
