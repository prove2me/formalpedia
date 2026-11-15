-- Prove2me | solution 2 for AvramDividend.Classical.avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:06:01.684392+00:00
-- url     : https://prove2.me/submissions/c2dd06dd-1d25-477c-993d-42cb093ca89d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped BigOperators
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
        ≤ ((1 : ℝ) / 2) ^ k) := by
  classical
  let ε : ℕ → ℝ := fun k => ((1 : ℝ) / 2) ^ k
  have hε (k : ℕ) : 0 < ε k := pow_pos (by norm_num) k
  let Ng : ℕ → ℕ := fun k => Classical.choose (hG (ε k) (hε k))
  let Nj : ℕ → ℕ := fun k => Classical.choose (hJ (ε k) (hε k))
  let Ne : ℕ → ℕ := fun k => Classical.choose (hE (ε k) (hε k))
  have hg (k m l : ℕ) (hm : Ng k ≤ m) (hl : Ng k ≤ l) :
      (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε k :=
    (Classical.choose_spec (hG (ε k) (hε k))) m l hm hl
  have hj (k m l : ℕ) (hm : Nj k ≤ m) (hl : Nj k ≤ l) :
      (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε k :=
    (Classical.choose_spec (hJ (ε k) (hε k))) m l hm hl
  have he (k m : ℕ) (hm : Ne k ≤ m) :
      (∫ ω, ‖E m ω‖ ∂P) ≤ ε k :=
    (Classical.choose_spec (hE (ε k) (hε k))) m hm
  let N : ℕ → ℕ := fun k => max (max (Ng k) (Nj k)) (Ne k)
  let K : ℕ → ℕ := Nat.rec (N 0) (fun k prev => max (prev + 1) (N (k + 1)))
  have hN (k : ℕ) : N k ≤ K k := by
    cases k with
    | zero => exact le_refl _
    | succ k => exact le_max_right _ _
  have hK : StrictMono K := strictMono_nat_of_lt_succ (by
    intro k
    exact (Nat.lt_succ_self (K k)).trans_le (le_max_left _ _))
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · intro k
    have h0 : Ng k ≤ K k := (le_max_left _ _).trans
      ((le_max_left _ _).trans (hN k))
    have h1 : Ng k ≤ K (k + 1) :=
      h0.trans (Nat.le_of_lt (hK (Nat.lt_succ_self k)))
    exact hg k (K (k + 1)) (K k) h1 h0
  · intro k
    have h0 : Nj k ≤ K k := (le_max_right _ _).trans
      ((le_max_left _ _).trans (hN k))
    have h1 : Nj k ≤ K (k + 1) :=
      h0.trans (Nat.le_of_lt (hK (Nat.lt_succ_self k)))
    exact hj k (K (k + 1)) (K k) h1 h0
  · intro k
    exact he k (K k) ((le_max_right _ _).trans (hN k))
