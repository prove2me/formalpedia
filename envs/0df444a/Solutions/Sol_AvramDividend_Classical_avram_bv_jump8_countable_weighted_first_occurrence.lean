-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_countable_weighted_first_occurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:36:49.644724+00:00
-- url     : https://prove2.me/submissions/35c4e4c6-9a5a-4d73-a9e0-f1df4971a2da

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Each covered time contributes its weight exactly at its first occurrence. -/
theorem solution
    (time : ℕ → ℝ≥0) (S : Set ℝ≥0)
    (hCover : S ⊆ Set.range time)
    (f : ℝ≥0 → ℝ≥0∞) :
    (∑' u : S, f (u : ℝ≥0)) =
      ∑' k : ℕ,
        if time k ∈ S ∧
          (∀ j : ℕ, j < k → time j ≠ time k)
        then f (time k) else 0 := by
  classical
  let A : Set ℕ :=
    {k | time k ∈ S ∧ ∀ j : ℕ, j < k → time j ≠ time k}
  have hInject : Set.InjOn time A := by
    intro i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hj.2 i hlt) heq
    · exact (hi.2 j hgt) heq.symm
  let e : A → S := fun k => ⟨time k, k.2.1⟩
  have hBij : Function.Bijective e := by
    constructor
    · intro i j heq
      apply Subtype.ext
      apply hInject i.2 j.2
      exact congrArg Subtype.val heq
    · intro u
      have hExists : ∃ n : ℕ, time n = u.1 := hCover u.2
      let n₀ := Nat.find hExists
      have hn₀ : time n₀ = u.1 := Nat.find_spec hExists
      have hnA : n₀ ∈ A := by
        constructor
        · rw [hn₀]
          exact u.2
        · intro j hj heq
          exact (Nat.find_min hExists hj) (heq.trans hn₀)
      exact ⟨⟨n₀, hnA⟩, Subtype.ext hn₀⟩
  let equiv : A ≃ S := Equiv.ofBijective e hBij
  calc
    (∑' u : S, f (u : ℝ≥0)) =
        ∑' k : A, f ((equiv k : S) : ℝ≥0) := by
          exact (equiv.tsum_eq (fun u : S => f (u : ℝ≥0))).symm
    _ = ∑' k : A, f (time k) := by rfl
    _ = ∑' k : ℕ, A.indicator (fun i : ℕ => f (time i)) k :=
      tsum_subtype A (fun i : ℕ => f (time i))
    _ = ∑' k : ℕ, if time k ∈ S ∧
            (∀ j : ℕ, j < k → time j ≠ time k)
          then f (time k) else 0 := by
      apply tsum_congr
      intro k
      by_cases hk : time k ∈ S ∧
          (∀ j : ℕ, j < k → time j ≠ time k)
      · have ha : k ∈ A := hk
        calc
          A.indicator (fun i : ℕ => f (time i)) k = f (time k) :=
            Set.indicator_of_mem ha _
          _ = (if time k ∈ S ∧
                 (∀ j : ℕ, j < k → time j ≠ time k)
               then f (time k) else 0) := (if_pos hk).symm
      · have ha : k ∉ A := hk
        calc
          A.indicator (fun i : ℕ => f (time i)) k = 0 :=
            Set.indicator_of_notMem ha _
          _ = (if time k ∈ S ∧
                 (∀ j : ℕ, j < k → time j ≠ time k)
               then f (time k) else 0) := (if_neg hk).symm
  all_goals
    apply tsum_congr
    intro k
    by_cases hk : time k ∈ S ∧
        (∀ j : ℕ, j < k → time j ≠ time k)
    · simp only [if_pos hk]
    · simp only [if_neg hk]
