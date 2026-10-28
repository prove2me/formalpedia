-- Prove2me | solution 1 for AvramDividend.Classical.positive_finite_ennreal_mass_ratio_subunit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:42:16.37361+00:00
-- url     : https://prove2.me/submissions/1977daa2-4fd1-4f20-ba72-287c4e915778

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

/-- A strictly positive subdrift ENNReal kernel mass yields a positive
subunit real normalised mass, the contraction parameter of renewal powers. -/
theorem solution
    (m : ℝ≥0∞) (δ : ℝ)
    (hδ : 0 < δ) (hmpos : 0 < m)
    (hmbound : m < ENNReal.ofReal δ) :
    0 < m.toReal / δ ∧ m.toReal / δ < 1 := by
  have hmfin : m ≠ ⊤ := ne_top_of_lt hmbound
  have hmrealpos : 0 < m.toReal :=
    ENNReal.toReal_pos (ne_of_gt hmpos) hmfin
  have hmrealbound : m.toReal < δ := by
    have hcmp : m.toReal < (ENNReal.ofReal δ).toReal :=
      (ENNReal.toReal_lt_toReal hmfin ENNReal.ofReal_ne_top).mpr hmbound
    simpa only [ENNReal.toReal_ofReal hδ.le] using hcmp
  exact ⟨div_pos hmrealpos hδ, (div_lt_one hδ).mpr hmrealbound⟩
