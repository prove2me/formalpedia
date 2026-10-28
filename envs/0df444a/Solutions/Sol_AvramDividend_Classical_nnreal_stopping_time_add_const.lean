-- Prove2me | solution 1 for AvramDividend.Classical.nnreal_stopping_time_add_const
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:34:39.525022+00:00
-- url     : https://prove2.me/submissions/291acaa9-2864-43be-9f54-7ff62147631d

import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) (h : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => τ ω + (h : WithTop ℝ≥0)) := by
  intro i
  by_cases hi : h ≤ i
  · have hset : {ω | τ ω + (h : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} =
        {ω | τ ω ≤ ((i - h : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      cases hω : τ ω with
      | top =>
        rw [WithTop.top_add]
        exact ⟨fun h' => absurd (top_le_iff.mp h') WithTop.coe_ne_top,
          fun h' => absurd (top_le_iff.mp h') WithTop.coe_ne_top⟩
      | coe x =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        exact (le_tsub_iff_right hi).symm
    rw [hset]
    exact 𝓕.mono tsub_le_self _ (hτ (i - h))
  · have hset : {ω | τ ω + (h : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      cases hω : τ ω with
      | top =>
        rw [hω, WithTop.top_add] at hle
        exact WithTop.coe_ne_top (top_le_iff.mp hle)
      | coe x =>
        rw [hω, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
        exact hi (le_trans le_add_self hle)
    rw [hset]
    exact @MeasurableSet.empty _ (𝓕 i)
