-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_original_subcap_V_to_w_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:48:28.813247+00:00
-- url     : https://prove2.me/submissions/d4b41802-3f1f-4c46-a894-24bdade63715

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

/-- On source-frozen cells below the cap, the cap extension has no overshoot. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ)
    (hStay : C ≠ ⊤ →
      z ≤ C.toReal ∧ z + d ≤ C.toReal) :
    V (z + d) - V z = w (z + d) - w z := by
  by_cases hC : C = ⊤
  · rw [hVtop hC (z + d), hVtop hC z]
  · obtain ⟨hz, hzd⟩ := hStay hC
    rw [hVfinite hC (z + d), hVfinite hC z,
        if_pos hzd, if_pos hz]
