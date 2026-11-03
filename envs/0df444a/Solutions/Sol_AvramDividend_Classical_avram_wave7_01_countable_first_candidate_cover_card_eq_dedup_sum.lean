-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:13:28.438255+00:00
-- url     : https://prove2.me/submissions/274dc6fd-6212-4628-a3a7-0f273e2f2178

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The first appearance of each covered jump time counts its set cardinality. -/
theorem solution
    (time : ℕ → ℝ≥0) (S : Set ℝ≥0)
    (hCover : S ⊆ Set.range time) :
    (S.encard : ℝ≥0∞) =
      ∑' k : ℕ,
        if time k ∈ S ∧
          (∀ j : ℕ, j < k → time j ≠ time k)
        then (1 : ℝ≥0∞) else 0 := by
  classical
  let A : Set ℕ :=
    {k | time k ∈ S ∧ ∀ j : ℕ, j < k → time j ≠ time k}
  have hInjective : Set.InjOn time A := by
    intro i hi j hj hEq
    by_contra hNe
    rcases lt_or_gt_of_ne hNe with hlt | hgt
    · exact (hj.2 i hlt) hEq
    · exact (hi.2 j hgt) hEq.symm
  have hImage : time '' A = S := by
    ext u
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk.1
    · intro hu
      have hExists : ∃ n : ℕ, time n = u := hCover hu
      let n₀ := Nat.find hExists
      have hN₀ : time n₀ = u := Nat.find_spec hExists
      refine ⟨n₀, ⟨?_, ?_⟩, hN₀⟩
      · rw [hN₀]
        exact hu
      · intro j hj hEq
        exact (Nat.find_min hExists hj) (hEq.trans hN₀)
  calc
    (S.encard : ℝ≥0∞) = ((time '' A).encard : ℝ≥0∞) := by
      rw [hImage]
    _ = (A.encard : ℝ≥0∞) := by
      exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞))
        hInjective.encard_image
    _ = ∑' k : A, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_set_one A).symm
    _ = ∑' k : ℕ,
          A.indicator (fun _ : ℕ => (1 : ℝ≥0∞)) k := by
      exact tsum_subtype A (fun _ : ℕ => (1 : ℝ≥0∞))
    _ = ∑' k : ℕ,
          if time k ∈ S ∧
            (∀ j : ℕ, j < k → time j ≠ time k)
          then (1 : ℝ≥0∞) else 0 := by
      apply tsum_congr
      intro k
      by_cases hk : time k ∈ S ∧
          (∀ j : ℕ, j < k → time j ≠ time k)
      · have ha : k ∈ A := hk
        calc
          A.indicator (fun _ : ℕ => (1 : ℝ≥0∞)) k = 1 :=
            Set.indicator_of_mem ha _
          _ = (if time k ∈ S ∧
                 (∀ j : ℕ, j < k → time j ≠ time k)
               then (1 : ℝ≥0∞) else 0) := (if_pos hk).symm
      · have ha : k ∉ A := hk
        calc
          A.indicator (fun _ : ℕ => (1 : ℝ≥0∞)) k = 0 :=
            Set.indicator_of_notMem ha _
          _ = (if time k ∈ S ∧
                 (∀ j : ℕ, j < k → time j ≠ time k)
               then (1 : ℝ≥0∞) else 0) := (if_neg hk).symm
  all_goals
    apply tsum_congr
    intro k
    by_cases hk : time k ∈ S ∧
        (∀ j : ℕ, j < k → time j ≠ time k)
    · simp only [if_pos hk]
    · simp only [if_neg hk]
