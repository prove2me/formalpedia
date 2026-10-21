-- Prove2me | solution 1 for AvramDividend.Classical.chat06_all_count_events_past_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:04:08.494022+00:00
-- url     : https://prove2.me/submissions/ae2af0f3-6fbd-460f-8091-e5943284bc01

import Mathlib.MeasureTheory.Constructions.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace AvramChat06

/-- Assemble zero-count and successor-count almost-sure past
cylinders into an interface uniform over every natural count.
All past observations have the common codomain ℕ→ℝ. -/
theorem all_count_events_from_zero_successor_cylinders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    ∀ k : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = k) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < k + 1 then τ i ω else 0) ∈ S) := by
  intro k
  cases k with
  | zero => simpa using hZero
  | succ n => simpa only [Nat.succ_eq_add_one] using hSucc n

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    ∀ k : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = k) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < k + 1 then τ i ω else 0) ∈ S) := by
  exact all_count_events_from_zero_successor_cylinders
    τ N hZero hSucc
