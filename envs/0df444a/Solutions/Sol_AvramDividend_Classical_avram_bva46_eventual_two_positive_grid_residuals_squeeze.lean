-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva46_eventual_two_positive_grid_residuals_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:54:44.715516+00:00
-- url     : https://prove2.me/submissions/b990a885-ee61-42dd-9488-19299858b6fc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva44_two_positive_error_residuals_squeeze

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical

/-- The one-sided squeeze tolerates a finite exceptional grid prefix. -/
theorem solution (E A B : ℕ → ℝ)
    (hbound : ∀ᶠ n in atTop, E n ≤ A n + B n)
    (hA : Tendsto (fun n => max (A n) 0) atTop (𝓝 0))
    (hB : Tendsto (fun n => max (B n) 0) atTop (𝓝 0)) :
    Tendsto (fun n => max (E n) 0) atTop (𝓝 0) := by
  let E' : ℕ → ℝ := fun n => min (E n) (A n + B n)
  have hbound' (n : ℕ) : E' n ≤ A n + B n := min_le_right _ _
  have hE' : Tendsto (fun n => max (E' n) 0) atTop (𝓝 0) :=
    avram_bva44_two_positive_error_residuals_squeeze E' A B hbound' hA hB
  have hEventually : (fun n => max (E' n) 0) =ᶠ[atTop]
      (fun n => max (E n) 0) := by
    filter_upwards [hbound] with n hn
    simp only [E', min_eq_left hn]
  exact hE'.congr' hEventually
