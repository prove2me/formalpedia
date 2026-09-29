-- Prove2me | solution 1 for Freiman.finite_limsup_subsequence_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:42:29.361877+00:00
-- url     : https://prove2.me/submissions/d0de86f7-8bc7-4323-9ed8-cabf701e1d92

import Definitions.Def_Freiman_lagrangeSpectrum
import Mathlib.Tactic.Linarith

open Freiman

set_option autoImplicit false

theorem solution (u v : ℕ → ℝ) (f : ℕ → ℕ) (t : ℝ)
    (hf : ∀ R : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R ≤ f n)
    (heq : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u (f n) = v n)
    (hupper : ∀ K : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      u q ≤ 2 ∨ ∃ n : ℕ, K ≤ n ∧ u q ≤ v n)
    (htwo : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 - ε < v n) :
    HasFiniteLimsup u t ↔ HasFiniteLimsup v t := by
  obtain ⟨N₀, hN₀⟩ := heq
  constructor
  · intro hu
    constructor
    · intro ε hε
      obtain ⟨R, hR⟩ := hu.1 ε hε
      obtain ⟨N, hN⟩ := hf R
      refine ⟨max N₀ N, ?_⟩
      intro n hn
      rw [← hN₀ n (le_trans (le_max_left _ _) hn)]
      exact hR (f n) (hN n (le_trans (le_max_right _ _) hn))
    · intro ε hε N
      rcases le_or_gt t 2 with ht | ht
      · obtain ⟨n, hn, hlarge⟩ := htwo ε hε N
        exact ⟨n, hn, by linarith⟩
      · have hδ : 0 < min ε (t - 2) := lt_min hε (sub_pos.mpr ht)
        obtain ⟨Q, hQ⟩ := hupper N
        obtain ⟨q, hq, hlarge⟩ := hu.2 (min ε (t - 2)) hδ Q
        have hmin₁ := min_le_left ε (t - 2)
        have hmin₂ := min_le_right ε (t - 2)
        rcases hQ q hq with hsmall | ⟨n, hn, hbound⟩
        · linarith
        · exact ⟨n, hn, by linarith⟩
  · intro hv
    have ht : 2 ≤ t := by
      by_contra h
      have hε : 0 < (2 - t) / 2 := by linarith
      obtain ⟨N, hN⟩ := hv.1 ((2 - t) / 2) hε
      obtain ⟨n, hn, hlarge⟩ := htwo ((2 - t) / 2) hε N
      have hsmall := hN n hn
      linarith
    constructor
    · intro ε hε
      obtain ⟨K, hK⟩ := hv.1 ε hε
      obtain ⟨Q, hQ⟩ := hupper K
      refine ⟨Q, ?_⟩
      intro q hq
      rcases hQ q hq with hsmall | ⟨n, hn, hbound⟩
      · linarith
      · exact hbound.trans (hK n hn)
    · intro ε hε N
      obtain ⟨R, hR⟩ := hf N
      obtain ⟨n, hn, hlarge⟩ := hv.2 ε hε (max N₀ R)
      refine ⟨f n, hR n (le_trans (le_max_right _ _) hn), ?_⟩
      rw [hN₀ n (le_trans (le_max_left _ _) hn)]
      exact hlarge
