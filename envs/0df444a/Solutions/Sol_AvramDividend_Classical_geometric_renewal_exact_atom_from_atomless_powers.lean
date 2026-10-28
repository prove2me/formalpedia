-- Prove2me | solution 1 for AvramDividend.Classical.geometric_renewal_exact_atom_from_atomless_powers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:01:01.551517+00:00
-- url     : https://prove2.me/submissions/cfe75902-577e-43a1-bd8a-ff00d0976741

import Theorems.Thm_AvramDividend_Classical_positive_atom_geometric_measure_sum
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The zeroth Dirac coefficient is the exact point mass when higher terms are atomless. -/
theorem solution
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : ℕ → Measure α) (c : ℝ≥0∞) (x : α)
    (hm0 : m 0 = Measure.dirac x)
    (hpositive : ∀ n : ℕ, 0 < n → m n {x} = 0) :
    (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) {x} = c := by
  classical
  rw [Measure.sum_apply _ (measurableSet_singleton x)]
  rw [tsum_eq_single (0 : ℕ)]
  · simp [hm0]
  · intro n hn
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    simp [hpositive n hpos]
