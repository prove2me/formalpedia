-- Prove2me | solution 1 for AvramDividend.Classical.chat03_generic_extended_infimum_lt_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:31:32.549615+00:00
-- url     : https://prove2.me/submissions/8ad521b1-ecf2-4e3e-adc3-8097ad771d97

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-!
The extended infimum over witness times is below a finite horizon
exactly when at least one witnessing time is below that horizon.
-/
theorem solution
    (p : ℝ≥0 → Prop) (T : ℝ≥0) :
    ((⨅ (s : ℝ≥0) (_ : p s), (s : ℝ≥0∞)) < (T : ℝ≥0∞)) ↔
      ∃ s : ℝ≥0, p s ∧ s < T := by
  simp only [iInf_lt_iff, ENNReal.coe_lt_coe]
  constructor
  · rintro ⟨s, hp, hst⟩
    exact ⟨s, hp, hst⟩
  · rintro ⟨s, hp, hst⟩
    exact ⟨s, hp, hst⟩

