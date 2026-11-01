-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:33:01.991828+00:00
-- url     : https://prove2.me/submissions/dd9b7f39-3069-4209-a01d-3efa01402337

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (mPast mFuture : ℕ → MeasurableSpace Ω)
    (hPastMono : Monotone mPast)
    (hFuturePast : ∀ i n, i < n → mFuture i ≤ mPast n)
    (H Z : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[mPast i] (H i))
    (hZ : ∀ i, StronglyMeasurable[mFuture i] (Z i))
    (n : ℕ) :
    StronglyMeasurable[mPast n]
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by
  have hSM : StronglyMeasurable[mPast n]
      (∑ i ∈ Finset.range n, fun ω => H i ω * Z i ω) := by
    apply Finset.stronglyMeasurable_sum (Finset.range n)
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hHn : StronglyMeasurable[mPast n] (H i) :=
      (hH i).mono (hPastMono (Nat.le_of_lt hin))
    have hZn : StronglyMeasurable[mPast n] (Z i) :=
      (hZ i).mono (hFuturePast i n hin)
    exact hHn.mul hZn
  have hfun :
      (∑ i ∈ Finset.range n, fun ω => H i ω * Z i ω) =
        (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [← hfun]
  exact hSM
