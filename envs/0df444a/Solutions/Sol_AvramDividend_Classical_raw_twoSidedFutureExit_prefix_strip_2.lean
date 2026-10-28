-- Prove2me | solution 2 for AvramDividend.Classical.raw_twoSidedFutureExit_prefix_strip
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:43:49.725303+00:00
-- url     : https://prove2.me/submissions/107d8a24-7a96-443c-a543-995837a710d4

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    (g : ℝ≥0 → ℝ) (ε a : ℝ) (ρ : ℝ≥0)
    (hUp : (ρ : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : ε < g t), (t : ℝ≥0∞)))
    (hBeforeDown : (ρ : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : g t < ε - a), (t : ℝ≥0∞))) :
    ∀ r : ℝ≥0, r < ρ → ε - a ≤ g r ∧ g r ≤ ε := by
  intro r hr
  have hr' : (r : ℝ≥0∞) < ρ := ENNReal.coe_lt_coe.2 hr
  constructor
  · by_contra h
    push_neg at h
    have : (⨅ (t : ℝ≥0) (_ : g t < ε - a), (t : ℝ≥0∞)) ≤ r := iInf₂_le r h
    exact absurd (lt_of_le_of_lt this hr') (not_lt.2 hBeforeDown.le)
  · by_contra h
    push_neg at h
    have : (⨅ (t : ℝ≥0) (_ : ε < g t), (t : ℝ≥0∞)) ≤ r := iInf₂_le r h
    rw [← hUp] at this
    exact absurd hr' (not_lt.2 this)
