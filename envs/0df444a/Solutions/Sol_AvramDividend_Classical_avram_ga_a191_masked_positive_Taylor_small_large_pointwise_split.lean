-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a191_masked_positive_Taylor_small_large_pointwise_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:13:34.77489+00:00
-- url     : https://prove2.me/submissions/ee2d22eb-7148-4f4a-8a9e-e7601d4f3adf

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_ga_a25_finite_sum_positive_part_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- True physical-mesh positive Taylor sums split pointwise between small
quadratic errors and arbitrary nonnegative large-tail envelopes. -/
theorem solution
    {Ω : Type*}
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (r e T : ℕ → Ω → ℝ)
    (ε M δ : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hT : ∀ i ω, 0 ≤ T i ω)
    (hSmall : ∀ i ω, A i ω → |r i ω| < δ →
      max (e i ω) 0 ≤ ε * (r i ω)^2)
    (hLarge : ∀ i ω, A i ω → δ ≤ |r i ω| →
      max (e i ω) 0 ≤ M * T i ω)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then e i ω else 0) 0 ≤
      ε * (∑ i ∈ S, if A i ω then (r i ω)^2 else 0) +
      M * (∑ i ∈ S, if A i ω then
        (if δ ≤ |r i ω| then T i ω else 0) else 0) := by
  classical
  calc
    max (∑ i ∈ S, if A i ω then e i ω else 0) 0 ≤
        ∑ i ∈ S, max (if A i ω then e i ω else 0) 0 :=
      avram_ga_a25_finite_sum_positive_part_le S
        (fun i => if A i ω then e i ω else 0)
    _ ≤ ∑ i ∈ S, ((if A i ω then
          ε * (r i ω)^2 else 0) +
          (if A i ω then
            (if δ ≤ |r i ω| then M * T i ω else 0) else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ha : A i ω
      · by_cases hδ : δ ≤ |r i ω|
        · simp only [if_pos ha, if_pos hδ]
          have hh := hLarge i ω ha hδ
          have hsmall_nonneg : 0 ≤ ε * (r i ω)^2 :=
            mul_nonneg hε (sq_nonneg _)
          have hlarge_nonneg : 0 ≤ M * T i ω :=
            mul_nonneg hM (hT i ω)
          linarith
        · have hlt : |r i ω| < δ := lt_of_not_ge hδ
          simpa [ha, hδ] using (hSmall i ω ha hlt)
      · simp [ha]
    _ = ε * (∑ i ∈ S, if A i ω then (r i ω)^2 else 0) +
        M * (∑ i ∈ S, if A i ω then
          (if δ ≤ |r i ω| then T i ω else 0) else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> ring
