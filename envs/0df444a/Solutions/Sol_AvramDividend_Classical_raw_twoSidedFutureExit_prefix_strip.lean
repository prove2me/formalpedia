-- Prove2me | solution 1 for AvramDividend.Classical.raw_twoSidedFutureExit_prefix_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:42:56.526516+00:00
-- url     : https://prove2.me/submissions/75b9eb5e-bc97-4b31-9369-0c5289933fc4

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Two-sided first-passage ordering confines the future path before its upper exit. -/
theorem solution
    (g : ℝ≥0 → ℝ) (ε a : ℝ) (ρ : ℝ≥0)
    (hUp : (ρ : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : ε < g t), (t : ℝ≥0∞)))
    (hBeforeDown : (ρ : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : g t < ε - a), (t : ℝ≥0∞))) :
    ∀ r : ℝ≥0, r < ρ → ε - a ≤ g r ∧ g r ≤ ε := by
  intro r hr
  have hrE : (r : ℝ≥0∞) < (ρ : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr hr
  constructor
  · by_contra hn
    have hCross : g r < ε - a := lt_of_not_ge hn
    have hInf :
        (⨅ (t : ℝ≥0) (_ : g t < ε - a), (t : ℝ≥0∞)) ≤
          (r : ℝ≥0∞) :=
      iInf_le_of_le r (iInf_le _ hCross)
    exact (not_lt_of_ge (le_of_lt hrE))
      (lt_of_lt_of_le hBeforeDown hInf)
  · by_contra hn
    have hCross : ε < g r := lt_of_not_ge hn
    have hInf :
        (⨅ (t : ℝ≥0) (_ : ε < g t), (t : ℝ≥0∞)) ≤
          (r : ℝ≥0∞) :=
      iInf_le_of_le r (iInf_le _ hCross)
    have hBad : (ρ : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by
      rw [hUp]
      exact hInf
    exact (not_le_of_gt hrE) hBad
