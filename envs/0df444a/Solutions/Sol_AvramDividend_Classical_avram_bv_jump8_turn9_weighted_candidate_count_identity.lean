-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn9_weighted_candidate_count_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:01:48.854213+00:00
-- url     : https://prove2.me/submissions/ff5e1684-6323-4276-b0fb-e469dcda2518

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_cadlag_true_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_countable_weighted_first_occurrence
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Weighted exact counting via the intrinsic mark map and first-visit bijection. -/
theorem solution
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hCandidate : ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (∀ k : ℕ, 0 < time k Y →
          mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
        (∀ u : ℝ≥0, 0 < u → Y u - Function.leftLim Y u ≠ 0 →
          ∃ k : ℕ, time k Y = u)) :
    ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      (∑' k : ℕ,
        if 0 < time k Y ∧ time k Y ≤ T ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then (if mark k Y = 0 then 0 else g (mark k Y))
        else 0) =
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
          (fun u => (u, Y u - Function.leftLim Y u))) := by
  intro Y hRight hLeft
  let jump : ℝ≥0 → ℝ := fun u => Y u - Function.leftLim Y u
  let S : Set ℝ≥0 := {u | 0 < u ∧ jump u ≠ 0}
  let originalMark : ℝ≥0 → ℝ≥0 × ℝ := fun u => (u, jump u)
  let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0
  have ⟨hMarkMeas, hSMeas⟩ :=
    avram_bv_jump8_turn9_cadlag_true_mark_measurable Y hRight hLeft
  have hFMeas : Measurable F := by
    have hPos : MeasurableSet
        (Prod.fst ⁻¹' Set.Ioi (0 : ℝ≥0) : Set (ℝ≥0 × ℝ)) :=
      measurableSet_Ioi.preimage measurable_fst
    have hBound : MeasurableSet
        (Prod.fst ⁻¹' Set.Iic T : Set (ℝ≥0 × ℝ)) :=
      measurableSet_Iic.preimage measurable_fst
    exact (hg.comp measurable_snd).ite (hPos.inter hBound) measurable_const
  have hCover : S ⊆ Set.range (fun k => time k Y) := by
    intro u hu
    obtain ⟨_, hCoverage⟩ := hCandidate Y hRight hLeft
    exact hCoverage u hu.1 hu.2
  let f : ℝ≥0 → ℝ≥0∞ := fun u => if u ≤ T then g (jump u) else 0
  have hReindex :=
    avram_bv_jump8_countable_weighted_first_occurrence
      (fun k => time k Y) S hCover f
  have hPointwise (k : ℕ) :
      (if 0 < time k Y ∧ time k Y ≤ T ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then (if mark k Y = 0 then 0 else g (mark k Y))
        else 0) =
      (if time k Y ∈ S ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then f (time k Y) else 0) := by
    obtain ⟨hExact, _⟩ := hCandidate Y hRight hLeft
    by_cases hpos : 0 < time k Y
    · rw [hExact k hpos]
      by_cases hzero :
          Y (time k Y) - Function.leftLim Y (time k Y) = 0
      · simp [S, f, jump, hpos, hzero]
      · by_cases hT : time k Y ≤ T
        <;> by_cases hFirst :
          (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        <;> simp [S, f, jump, hpos, hzero, hT, hFirst]
    · simp [S, f, hpos]
  calc
    (∑' k : ℕ, if 0 < time k Y ∧ time k Y ≤ T ∧
        (∀ j : ℕ, j < k → time j Y ≠ time k Y)
      then (if mark k Y = 0 then 0 else g (mark k Y))
      else 0) =
      ∑' k : ℕ, if time k Y ∈ S ∧
          (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then f (time k Y) else 0 := by exact tsum_congr hPointwise
    _ = ∑' u : S, f u := by
      apply Eq.trans ?_ hReindex.symm
      apply tsum_congr
      intro k
      by_cases hk : time k Y ∈ S ∧
          (∀ j : ℕ, j < k → time j Y ≠ time k Y)
      · simp [hk]
      · simp [hk]
    _ = ∑' u : ℝ≥0, if u ∈ S then F (originalMark u) else 0 := by
      rw [tsum_subtype]
      apply tsum_congr
      intro u
      by_cases hu : u ∈ S
      · simp [Set.indicator, hu, S, F, originalMark, f, hu.1]
      · simp [Set.indicator, hu]
    _ = ∫⁻ p, F p ∂((Measure.count.restrict S).map originalMark) := by
      apply Eq.trans ?_
        ((avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
          S hSMeas originalMark hMarkMeas F hFMeas).symm)
      apply tsum_congr
      intro u
      by_cases hu : u ∈ S
      · simp [hu]
      · simp [hu]
    _ = _ := rfl
