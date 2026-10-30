-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_conull_positive_additive_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:04:48.697692+00:00
-- url     : https://prove2.me/submissions/a4ea764a-33f7-4f63-a8c3-5c5d6b622f93

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A full-Lebesgue-measure set of positive times additively covers every
positive time. This is the exact time-upgrade step for the actual killed
q-scale semigroup, after its genuine stochastic resolvent and composition
identities have been proved. -/
theorem solution (G : Set ℝ)
    (hG : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ G) :
    ∀ t : ℝ, 0 < t →
      ∃ s ∈ G, ∃ u ∈ G, 0 < s ∧ 0 < u ∧ s + u = t := by
  classical
  have hNull : (volume : Measure ℝ) Gᶜ = 0 := (ae_iff).mp hG
  have hNeg :
      (volume : Measure ℝ) ((fun y : ℝ => -y) ⁻¹' Gᶜ) = 0 := by
    rw [Measure.measure_preimage_neg]
    exact hNull
  intro t ht
  have hTranslate :
      (volume : Measure ℝ)
        ((fun s : ℝ => s + (-t)) ⁻¹'
          ((fun y : ℝ => -y) ⁻¹' Gᶜ)) = 0 := by
    rw [measure_preimage_add_right]
    exact hNeg
  have hSet :
      {s : ℝ | t - s ∈ Gᶜ} =
        (fun s : ℝ => s + (-t)) ⁻¹'
          ((fun y : ℝ => -y) ⁻¹' Gᶜ) := by
    ext s
    change (t - s ∈ Gᶜ) ↔ (-(s + -t) ∈ Gᶜ)
    rw [show -(s + -t) = t - s by ring]
  have hReflect :
      (volume : Measure ℝ) {s : ℝ | t - s ∈ Gᶜ} = 0 := by
    rw [hSet]
    exact hTranslate
  by_contra hNo
  have hCover :
      Ioo (0 : ℝ) t ⊆ Gᶜ ∪ {s : ℝ | t - s ∈ Gᶜ} := by
    intro s hs
    by_cases hsG : s ∈ G
    · by_cases huG : t - s ∈ G
      · exfalso
        apply hNo
        refine ⟨s, hsG, t - s, huG, hs.1, sub_pos.mpr hs.2, ?_⟩
        ring
      · exact Or.inr huG
    · exact Or.inl hsG
  have hZero : (volume : Measure ℝ) (Ioo (0 : ℝ) t) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      (volume : Measure ℝ) (Ioo (0 : ℝ) t) ≤
        (volume : Measure ℝ) (Gᶜ ∪ {s : ℝ | t - s ∈ Gᶜ}) :=
          measure_mono hCover
      _ ≤ (volume : Measure ℝ) Gᶜ +
          (volume : Measure ℝ) {s : ℝ | t - s ∈ Gᶜ} :=
            measure_union_le _ _
      _ = 0 := by rw [hNull, hReflect, add_zero]
  have hPos : 0 < (volume : Measure ℝ) (Ioo (0 : ℝ) t) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by simpa using ht)
  exact (not_lt_of_ge (le_of_eq hZero)) hPos
