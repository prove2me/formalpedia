-- Prove2me | solution 1 for Freiman.maximal_hall_ray
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T09:53:40.534489+00:00
-- url     : https://prove2.me/submissions/a7fb8595-2fac-4399-b18e-685b39659967

import Theorems.Thm_Freiman_constant_order
import Theorems.Thm_Freiman_lower_interval
import Theorems.Thm_Freiman_middle_interval
import Theorems.Thm_Freiman_upper_ray
import Theorems.Thm_Freiman_exact_gap
import Theorems.Thm_Freiman_lagrange_subset_markov
import Mathlib.Tactic.Linarith

open Freiman

set_option autoImplicit false

theorem solution :
    (∀ d : ℝ, Set.Ici d ⊆ lagrangeSpectrum ↔ cF ≤ d) ∧
    (∀ d : ℝ, Set.Ici d ⊆ markovSpectrum ↔ cF ≤ d) := by
  obtain ⟨hgap₁, hgap₂, _, _, hupper⟩ := constant_order
  have hgap : gapLeft < cF := lt_trans hgap₁ hgap₂
  have hL : Set.Ici cF ⊆ lagrangeSpectrum := by
    intro x hx
    change cF ≤ x at hx
    by_cases h₁ : x ≤ Real.sqrt 21
    · exact lower_interval ⟨hx, h₁⟩
    by_cases h₂ : x ≤ (128 / 25 : ℝ)
    · exact middle_interval ⟨le_of_not_ge h₁, h₂⟩
    · exact upper_ray (le_trans (le_of_lt hupper) (le_of_not_ge h₂))
  have hM : Set.Ici cF ⊆ markovSpectrum :=
    fun _ hx => lagrange_subset_markov (hL hx)
  have hmax (S : Set ℝ) (hSM : S ⊆ markovSpectrum)
      (hray : Set.Ici cF ⊆ S) (d : ℝ) :
      Set.Ici d ⊆ S ↔ cF ≤ d := by
    constructor
    · intro hd
      by_contra hdc
      have hdlt : d < cF := lt_of_not_ge hdc
      let x : ℝ := (max d gapLeft + cF) / 2
      have hm : max d gapLeft < cF := max_lt hdlt hgap
      have hdx : d ≤ x := by dsimp [x]; linarith [le_max_left d gapLeft]
      have hgx : gapLeft < x := by
        dsimp [x]; linarith [le_max_right d gapLeft]
      have hxc : x < cF := by dsimp [x]; linarith
      have hx : x ∈ markovSpectrum ∩ Set.Ioo gapLeft cF :=
        ⟨hSM (hd hdx), hgx, hxc⟩
      rw [exact_gap.2.2] at hx
      exact hx
    · intro hdc x hx
      exact hray (le_trans hdc hx)
  exact ⟨hmax lagrangeSpectrum lagrange_subset_markov hL,
    hmax markovSpectrum (fun _ h => h) hM⟩
