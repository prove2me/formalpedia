-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:32:22.713716+00:00
-- url     : https://prove2.me/submissions/6705a433-fa1a-439f-9d0b-3d65083e0e6a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal

namespace S214E57

def fsum {n : ℕ} (v : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if i.val < k then v i else 0

lemma fsum_eq {n : ℕ} (h : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    fsum (fun i : Fin n => h i.val) k = ∑ j ∈ Finset.range k, h j := by
  unfold fsum
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then h j else 0) n, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  congr 1
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma meas (n : ℕ) (a : ℝ) :
    MeasurableSet {v : Fin n → ℝ | ∃ k : Fin n.succ, fsum v k.val < a} := by
  have : {v : Fin n → ℝ | ∃ k : Fin n.succ, fsum v k.val < a} =
      ⋃ k : Fin n.succ, {v | fsum v k.val < a} := by ext; simp
  rw [this]
  refine MeasurableSet.iUnion fun k => measurableSet_lt ?_ measurable_const
  unfold fsum
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : i.val < k.val <;> simp only [h, if_true, if_false] <;> fun_prop

end S214E57

open S214E57 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ)
    (ν : Measure Ω) (a : ℝ)
    (hR : ∀ A : Set (Fin n → ℝ), MeasurableSet A →
      ν {ω : Ω | (fun i : Fin n =>
        X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A} =
      ν {ω : Ω | (fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A}) :
    ν {ω : Ω | ∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω - X.X ((k.val : ℝ≥0) * δ) ω < a} =
    ν {ω : Ω | ∃ k : Fin n.succ,
      X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω < a} := by
  set g : Ω → ℕ → ℝ := fun ω j =>
    X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω - X.X ((j : ℝ≥0) * δ) ω with hg
  have tel : ∀ ω (k : ℕ), X.X ((k : ℝ≥0) * δ) ω - X.X 0 ω = ∑ j ∈ Finset.range k, g ω j := by
    intro ω k
    have := Finset.sum_range_sub (fun j : ℕ => X.X ((j : ℝ≥0) * δ) ω) k
    simp only [Nat.cast_zero, zero_mul] at this
    rw [← this]
  set A2 := {v : Fin n → ℝ | ∃ k : Fin n.succ, fsum v k.val < a}
  have hRHS : {ω : Ω | ∃ k : Fin n.succ, X.X ((k.val : ℝ≥0) * δ) ω - X.X 0 ω < a} =
      {ω : Ω | (fun i : Fin n => X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, A2]
    refine exists_congr fun k => ?_
    rw [tel, fsum_eq (g ω) k.val (Nat.lt_succ_iff.mp k.isLt)]
  have hLHS : {ω : Ω | ∃ k : Fin n.succ,
      X.X ((n : ℝ≥0) * δ) ω - X.X ((k.val : ℝ≥0) * δ) ω < a} =
      {ω : Ω | (fun i : Fin n => X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, A2]
    have hr := AvramDividend.Classical.finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b
      (g ω) n
    have e1 : ∀ k : Fin n.succ, X.X ((n : ℝ≥0) * δ) ω - X.X ((k.val : ℝ≥0) * δ) ω =
        ∑ j ∈ Finset.range n, g ω j - ∑ j ∈ Finset.range k.val, g ω j := by
      intro k; rw [← tel, ← tel]; ring
    have e2 : ∀ k : Fin n.succ, fsum (fun i : Fin n => X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) k.val = ∑ j ∈ Finset.range k.val, g ω (n - 1 - j) := by
      intro k
      rw [← fsum_eq (fun j => g ω (n - 1 - j)) k.val (Nat.lt_succ_iff.mp k.isLt)]
      unfold fsum
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : n - (i.val + 1) = n - 1 - i.val := by omega
      simp only [Fin.val_rev, hg, h1]
    simp only [e1, e2]
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨m, hm⟩ : (∑ j ∈ Finset.range n, g ω j - ∑ j ∈ Finset.range k.val, g ω j) ∈
          Set.range (fun k : Fin n.succ => ∑ j ∈ Finset.range k.val, g ω (n - 1 - j)) := by
        rw [← hr]; exact ⟨k, rfl⟩
      exact ⟨m, by simp only at hm; rw [hm]; exact hk⟩
    · rintro ⟨k, hk⟩
      obtain ⟨m, hm⟩ : (∑ j ∈ Finset.range k.val, g ω (n - 1 - j)) ∈
          Set.range (fun k : Fin n.succ => ∑ j ∈ Finset.range n, g ω j -
            ∑ j ∈ Finset.range k.val, g ω j) := by
        rw [hr]; exact ⟨k, rfl⟩
      exact ⟨m, by simp only at hm; rw [hm]; exact hk⟩
  rw [hLHS, hRHS]
  exact hR A2 (meas n a)
