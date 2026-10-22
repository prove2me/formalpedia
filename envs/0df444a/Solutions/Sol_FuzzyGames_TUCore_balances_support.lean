-- Prove2me | solution 1 for FuzzyGames.TUCore.balances_support
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:27:36.432129+00:00
-- url     : https://prove2.me/submissions/5cbee1f4-450e-4522-86d8-0abfa725cd6c

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

set_option autoImplicit false

theorem solution {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (τ : Fin n → ℝ)
    (m : Finset (Fin n) → ℝ) (hm : m ∈ FuzzyGames.NTUCore.balances 𝒞 τ) (A : Finset (Fin n)) (hA : 0 < m A) :
    A ⊆ Finset.univ.filter (fun i => 0 < τ i) := by
  obtain ⟨hnn, hsupp, hsum⟩ := hm
  have hAC : A ∈ 𝒞.C := by
    by_contra h
    have := hsupp A h
    linarith
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hsum i]
  have hmem : A ∈ 𝒞.C.filter (fun A => i ∈ A) := by
    simp [hAC, hi]
  calc (0:ℝ) < m A := hA
    _ ≤ ∑ B ∈ 𝒞.C.filter (fun A => i ∈ A), m B :=
        Finset.single_le_sum (f := m) (fun B _ => hnn B) hmem
