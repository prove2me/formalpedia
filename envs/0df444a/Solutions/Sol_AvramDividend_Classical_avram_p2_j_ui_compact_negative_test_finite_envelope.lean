-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_compact_negative_test_finite_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:22:38.116104+00:00
-- url     : https://prove2.me/submissions/7dc1c57d-6f89-4cb4-91b2-7105d36c8daa

import Mathlib.Analysis.Normed.Group.Real
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_separation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal

/-! Compact negative continuous tests have a finite separated ENNReal envelope. -/
theorem solution
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ENNReal, M ≠ ⊤ ∧
      ∀ y : ℝ, ‖g y‖ₑ ≤ if y ≤ -ε then M else 0 := by
  classical
  obtain ⟨ε, hε, hgap⟩ :=
    avram_p2_j_ui_compact_negative_support_separation
      (tsupport g) hc hneg
  by_cases hne : (tsupport g).Nonempty
  · obtain ⟨x, hx, hmax⟩ :=
      hc.exists_isMaxOn hne (f := fun z : ℝ => |g z|)
        hg.abs.continuousOn
    refine ⟨ε, hε, ENNReal.ofReal (|g x|), ENNReal.ofReal_ne_top, ?_⟩
    intro y
    by_cases hy : y ∈ tsupport g
    · rw [if_pos (hgap y hy), Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hmax hy)
    · have hz : g y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hz]
  · refine ⟨ε, hε, 0, by simp, ?_⟩
    intro y
    have hy : y ∉ tsupport g := by
      intro hy
      exact hne ⟨y, hy⟩
    have hz : g y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [hz]
