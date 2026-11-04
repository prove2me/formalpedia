-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:15:08.786507+00:00
-- url     : https://prove2.me/submissions/76902f85-45ee-440d-a24c-894ad60e2fd9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For finite total mass, real-valued reciprocal ENNReal cutoff totals increase
to the full real-valued mass, with no countability hypothesis on indices. -/
theorem solution
    {α : Type*} (f : α → ℝ≥0∞) (hfinite : (∑' a : α, f a) < ⊤) :
    (⨆ n : ℕ, (∑' a : α,
      if (n : ℝ≥0∞)⁻¹ < f a then f a else 0).toReal) =
      (∑' a : α, f a).toReal := by
  classical
  have hbelow (n : ℕ) :
      (∑' a : α, if (n : ℝ≥0∞)⁻¹ < f a then f a else 0) < ⊤ := by
    have hle :
        (∑' a : α, if (n : ℝ≥0∞)⁻¹ < f a then f a else 0) ≤
          (∑' a : α, f a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases h : (n : ℝ≥0∞)⁻¹ < f a
      · simp [h]
      · simp [h]
    exact lt_of_le_of_lt hle hfinite
  calc
    (⨆ n : ℕ, (∑' a : α,
      if (n : ℝ≥0∞)⁻¹ < f a then f a else 0).toReal) =
        ((⨆ n : ℕ, ∑' a : α,
          if (n : ℝ≥0∞)⁻¹ < f a then f a else 0) : ℝ≥0∞).toReal := by
          symm
          exact ENNReal.toReal_iSup (fun n => ne_of_lt (hbelow n))
    _ = (∑' a : α, f a).toReal := by
          rw [avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full]
