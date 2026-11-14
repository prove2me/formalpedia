-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB249_continuous_minus_BV_offrange_occupation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:31.432395+00:00
-- url     : https://prove2.me/submissions/2952a874-5061-4293-9f1a-e754eae373ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB245_continuous_source_minus_locally_BV_reserve_compact_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Compact reserve path range forces off-range stopped spatial occupation to vanish. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) (n : ℕ) (ρ : ℝ≥0) :
    ∃ lo hi : ℝ, ∀ a b : ℝ, (hi ≤ a ∨ b ≤ lo) →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ : ℝ) ∧
        x + f (Real.toNNReal t) -
          d (Real.toNNReal t) ∈ Set.Ioo a b} = 0 := by
  obtain ⟨lo, hi, hRange⟩ :=
    avram_gbB245_continuous_source_minus_locally_BV_reserve_compact_bound
      f hf d hd x (n : ℝ≥0)
  refine ⟨lo, hi, ?_⟩
  intro a b hOutside
  have hEmpty :
      {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ : ℝ) ∧
        x + f (Real.toNNReal t) -
          d (Real.toNNReal t) ∈ Set.Ioo a b} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨ht0, htn, htρ, hclip⟩
    have htt : (Real.toNNReal t) ≤ (n : ℝ≥0) := by
      apply (Real.toNNReal_le_iff_le_coe).2
      exact_mod_cast (le_of_lt htn)
    have hb := hRange (Real.toNNReal t)
      ⟨bot_le, htt⟩
    rcases hOutside with ha | hb'
    · exact (not_lt_of_ge (hb.2.trans ha)) hclip.1
    · exact (not_lt_of_ge (hb'.trans hb.1)) hclip.2
  rw [hEmpty]
  exact measure_empty
