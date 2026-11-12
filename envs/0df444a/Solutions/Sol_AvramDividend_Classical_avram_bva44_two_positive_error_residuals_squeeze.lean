-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva44_two_positive_error_residuals_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:02:01.597239+00:00
-- url     : https://prove2.me/submissions/982387de-f3ac-4d1c-aa91-57d480bb8d5b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- A sum of two independently controlled positive errors still vanishes. -/
theorem solution (E A B : ℕ → ℝ) (hbound : ∀ n, E n ≤ A n + B n)
    (hA : Tendsto (fun n => max (A n) 0) atTop (𝓝 0))
    (hB : Tendsto (fun n => max (B n) 0) atTop (𝓝 0)) :
    Tendsto (fun n => max (E n) 0) atTop (𝓝 0) := by
  have hupper (n : ℕ) :
      max (E n) 0 ≤ max (A n) 0 + max (B n) 0 := by
    have hAa : A n ≤ max (A n) 0 := le_max_left _ _
    have hBb : B n ≤ max (B n) 0 := le_max_left _ _
    have hposA : 0 ≤ max (A n) 0 := le_max_right _ _
    have hposB : 0 ≤ max (B n) 0 := le_max_right _ _
    exact max_le (le_trans (hbound n) (add_le_add hAa hBb))
      (add_nonneg hposA hposB)
  have hnonneg (n : ℕ) : 0 ≤ max (E n) 0 := le_max_right _ _
  have hsum : Tendsto
      (fun n => max (A n) 0 + max (B n) 0) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hA.add hB
  have hleft : (fun _ : ℕ => (0 : ℝ)) ≤
      (fun n => max (E n) 0) := hnonneg
  have hright : (fun n => max (E n) 0) ≤
      (fun n => max (A n) 0 + max (B n) 0) := hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum hleft hright
