-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_count_residual_cylinder_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:12:14.718202+00:00
-- url     : https://prove2.me/submissions/68d1b73f-b70e-45d6-9c0a-d80cbfd5c0b7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The renewal residual-survival cylinder formula holds outside the same joint null set. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (n : ℕ) (Q : Set Ω) (t : ℝ) (ht : 0 ≤ t) :
    {ω | ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)} =ᵐ[P]
    {ω | ω ∈ Q ∧ (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
  filter_upwards [hThresholdAE] with ω hThreshold
  apply propext
  have hCyl :=
    AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
      (fun i => τ i ω) (N ω) hThreshold clock hclock n
  change
    (ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)) ↔
    (ω ∈ Q ∧ (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω)
  rw [Finset.sum_range_succ]
  constructor
  · rintro ⟨hq, hn, hsurv⟩
    have hBefore := (hCyl.mp hn).1
    exact ⟨hq, hBefore, by linarith⟩
  · rintro ⟨hq, hBefore, hsurv⟩
    have hBeyond : clock <
        (∑ i ∈ Finset.range n, τ i ω) + τ n ω := by linarith
    have hn := hCyl.mpr
      ⟨hBefore, by simpa only [Finset.sum_range_succ] using hBeyond⟩
    exact ⟨hq, hn, by linarith⟩
