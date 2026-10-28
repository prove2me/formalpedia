-- Prove2me | solution 1 for AvramDividend.Classical.geometric_renewal_origin_atom_of_powers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:59:22.822787+00:00
-- url     : https://prove2.me/submissions/a20e5511-65e0-4471-9051-bf799148851a

import Theorems.Thm_AvramDividend_Classical_geometric_renewal_positive_convolution_powers_no_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Compute the only surviving atomic term of the geometric renewal measure. -/
theorem solution
    (c : ℝ≥0∞) (m : ℕ → Measure ℝ)
    (hm0 : m 0 = Measure.dirac 0)
    (hrest : ∀ n : ℕ, 0 < n → m n ({(0 : ℝ)} : Set ℝ) = 0) :
    (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n))
      ({(0 : ℝ)} : Set ℝ) = c := by
  rw [Measure.sum_apply_of_countable]
  have hvanish :
      ∀ n : ℕ, n ≠ 0 →
        (c ^ (n + 1) • m n) ({(0 : ℝ)} : Set ℝ) = 0 := by
    intro n hn
    simp [hrest n (Nat.pos_of_ne_zero hn)]
  rw [tsum_eq_single 0 hvanish]
  simp [hm0]
