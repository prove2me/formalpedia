-- Prove2me | solution 1 for AvramDividend.Classical.geometric_renewal_positive_convolution_powers_no_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:37:39.417004+00:00
-- url     : https://prove2.me/submissions/4bd0d9b5-e5af-4ada-8741-4a922506c9c9

import Theorems.Thm_AvramDividend_Classical_renewal_measure_ac_on_positive
import Mathlib.MeasureTheory.Group.Convolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive-order renewal convolution powers are atomless at zero. -/
theorem solution
    (κ : Measure ℝ) [SFinite κ] (m : ℕ → Measure ℝ)
    (hmsf : ∀ n : ℕ, SFinite (m n))
    (hκ : κ ≪ (volume : Measure ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n)) :
    ∀ n : ℕ, 0 < n → m n ({(0 : ℝ)} : Set ℝ) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  haveI : SFinite (m k) := hmsf k
  have hac : (m k).conv κ ≪ (volume : Measure ℝ) :=
    Measure.conv_absolutelyContinuous hκ
  rw [hmsucc k, Measure.conv_comm]
  exact hac (by simp)
