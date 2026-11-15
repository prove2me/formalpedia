-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_two_channel_L1_cauchy_positive_error_geometric_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:12:43.540854+00:00
-- url     : https://prove2.me/submissions/4b6a20c9-88d9-4f30-a1ba-51b0d3c83554

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G J E : ℕ → Ω → ℝ)
    (hGC : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l →
        (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε)
    (hJC : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l →
        (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
    (hEC : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖E m ω‖ ∂P) ≤ ε) :
    ∃ s : ℕ → ℕ,
      (∀ k, s k < s (k + 1)) ∧
      (∀ k, (∫ ω, ‖G (s (k + 1)) ω - G (s k) ω‖ ∂P) ≤
        ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖J (s (k + 1)) ω - J (s k) ω‖ ∂P) ≤
        ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖E (s k) ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) := by
  classical
  have hThreshold (k : ℕ) :
      ∃ N : ℕ,
        (∀ m l, N ≤ m → N ≤ l →
          (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧
        (∀ m l, N ≤ m → N ≤ l →
          (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧
        (∀ m, N ≤ m →
          (∫ ω, ‖E m ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) := by
    have hp : 0 < ((1 : ℝ) / 2) ^ k := pow_pos (by norm_num) _
    obtain ⟨ng, hg⟩ := hGC _ hp
    obtain ⟨nj, hj⟩ := hJC _ hp
    obtain ⟨ne, he⟩ := hEC _ hp
    refine ⟨max ng (max nj ne), ?_, ?_, ?_⟩
    · intro m l hm hl
      exact hg m l (le_trans (le_max_left _ _) hm)
        (le_trans (le_max_left _ _) hl)
    · intro m l hm hl
      have hjBound : nj ≤ max ng (max nj ne) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      exact hj m l (le_trans hjBound hm) (le_trans hjBound hl)
    · intro m hm
      have heBound : ne ≤ max ng (max nj ne) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact he m (le_trans heBound hm)
  let N : ℕ → ℕ := fun k => Classical.choose (hThreshold k)
  have hNSpec (k : ℕ) := Classical.choose_spec (hThreshold k)
  let s : ℕ → ℕ :=
    Nat.rec (N 0) (fun k prev => max (prev + 1) (N (k + 1)))
  have hsBound (k : ℕ) : N k ≤ s k := by
    induction k with
    | zero => exact le_refl _
    | succ k ih =>
      change N (k + 1) ≤ max (s k + 1) (N (k + 1))
      exact le_max_right _ _
  have hsStep (k : ℕ) : s k < s (k + 1) := by
    change s k < max (s k + 1) (N (k + 1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  refine ⟨s, hsStep, ?_, ?_, ?_⟩
  · intro k
    have hsNext : N k ≤ s (k + 1) :=
      le_trans (hsBound k) (Nat.le_of_lt (hsStep k))
    exact (hNSpec k).1 (s (k + 1)) (s k) hsNext (hsBound k)
  · intro k
    have hsNext : N k ≤ s (k + 1) :=
      le_trans (hsBound k) (Nat.le_of_lt (hsStep k))
    exact (hNSpec k).2.1 (s (k + 1)) (s k) hsNext (hsBound k)
  · intro k
    exact (hNSpec k).2.2 (s k) (hsBound k)
