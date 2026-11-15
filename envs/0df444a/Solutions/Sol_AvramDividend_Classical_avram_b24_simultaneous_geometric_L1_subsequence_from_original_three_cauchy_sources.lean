-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:05:34.818244+00:00
-- url     : https://prove2.me/submissions/70bb497a-0eab-439d-841f-541531c33057

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped BigOperators NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J E : ℕ → Ω → ℝ)
    (hG : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l : ℕ, N ≤ m → N ≤ l →
        (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε)
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l : ℕ, N ≤ m → N ≤ l →
        (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖E m ω‖ ∂P) ≤ ε) :
    ∃ K : ℕ → ℕ, StrictMono K ∧
      (∀ k, (∫ ω, ‖G (K (k + 1)) ω - G (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖J (K (k + 1)) ω - J (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖E (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k)  := by
  classical
  have hThreshold : ∀ k : ℕ, ∃ N : ℕ,
      (∀ m l : ℕ, N ≤ m → N ≤ l →
        (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ m l : ℕ, N ≤ m → N ≤ l →
        (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ m : ℕ, N ≤ m →
        (∫ ω, ‖E m ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) := by
    intro k
    have hrate : 0 < ((1 : ℝ) / 2) ^ k := by
      apply pow_pos
      norm_num
    obtain ⟨NG, hNG⟩ := hG _ hrate
    obtain ⟨NJ, hNJ⟩ := hJ _ hrate
    obtain ⟨NE, hNE⟩ := hE _ hrate
    refine ⟨max NG (max NJ NE), ?_, ?_, ?_⟩
    · intro m l hm hl
      exact hNG m l ((le_max_left _ _).trans hm)
        ((le_max_left _ _).trans hl)
    · intro m l hm hl
      have hsmall : NJ ≤ max NG (max NJ NE) :=
        (le_max_left _ _).trans (le_max_right _ _)
      exact hNJ m l (hsmall.trans hm) (hsmall.trans hl)
    · intro m hm
      have hsmall : NE ≤ max NG (max NJ NE) :=
        (le_max_right _ _).trans (le_max_right _ _)
      exact hNE m (hsmall.trans hm)
  choose N hN using hThreshold
  let K : ℕ → ℕ :=
    Nat.rec (N 0) (fun k last => max (last + 1) (N (k + 1)))
  have hstep (k : ℕ) :
      K (k + 1) = max (K k + 1) (N (k + 1)) := rfl
  have hKN (k : ℕ) : N k ≤ K k := by
    cases k with
    | zero => rfl
    | succ k =>
        rw [hstep]
        exact le_max_right _ _
  have hnext (k : ℕ) : K k ≤ K (k + 1) := by
    rw [hstep]
    exact (Nat.le_succ _).trans (le_max_left _ _)
  have hStrict : StrictMono K := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hstep]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  refine ⟨K, hStrict, ?_, ?_, ?_⟩
  · intro k
    exact (hN k).1 (K (k + 1)) (K k)
      ((hKN k).trans (hnext k)) (hKN k)
  · intro k
    exact (hN k).2.1 (K (k + 1)) (K k)
      ((hKN k).trans (hnext k)) (hKN k)
  · intro k
    exact (hN k).2.2 (K k) (hKN k)
