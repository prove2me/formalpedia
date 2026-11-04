-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_l2_uniform_l1_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:29:10.848093+00:00
-- url     : https://prove2.me/submissions/43b03881-d322-48ad-a9c4-7d6c249b4467

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! A finite uniform L² seminorm envelope gives genuine L¹ moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal)) :
    ∀ n, Integrable (Y n) P ∧
      eLpNorm (Y n) 1 P ≤ (B : ENNReal) := by
  intro n
  have h2 : MemLp (Y n) 2 P :=
    ⟨hm n, lt_of_le_of_lt (hB n) (by simp)⟩
  have h1 : MemLp (Y n) 1 P := h2.mono_exponent (by norm_num)
  have hi : Integrable (Y n) P := memLp_one_iff_integrable.mp h1
  have hb : eLpNorm (Y n) 1 P ≤ (B : ENNReal) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hm n)).trans (hB n)
  exact ⟨hi, hb⟩
