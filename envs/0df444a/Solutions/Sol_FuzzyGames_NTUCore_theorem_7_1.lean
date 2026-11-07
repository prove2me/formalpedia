-- Prove2me | solution 1 for FuzzyGames.NTUCore.theorem_7_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:41:56.258196+00:00
-- url     : https://prove2.me/submissions/93f053d5-7e91-4e59-a60b-b736bb66dd44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic
import Theorems.Thm_FuzzyGames_NTUCore_theorem_5_1
import Theorems.Thm_FuzzyGames_NTUCore_theorem_3_1
import Theorems.Thm_FuzzyGames_NTUCore_piV_closed_convex
import Theorems.Thm_FuzzyGames_NTUCore_eq_7_7
import Theorems.Thm_FuzzyGames_NTUCore_core_piV_subset_core
import Theorems.Thm_FuzzyGames_NTUCore_cce_eq_piV_cce

open Set Finset Pointwise

open FuzzyGames.NTUCore in
theorem solution {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (hbal : IsBalanced 𝒞 V) :
    (ntuCore 𝒞 V).Nonempty ∧
      (fuzzyCore (piV 𝒞 V)).Nonempty ∧ fuzzyCore (piV 𝒞 V) ⊆ ntuCore 𝒞 V ∧
      ntuStrongCCE 𝒞 V ⊆ fuzzyCore (piV 𝒞 V) ∧
      fuzzyCore (piV 𝒞 V) ⊆ ntuWeakCCE 𝒞 V := by
  -- `n ≥ 1`, since `N ∈ 𝒞` and `∅ ∉ 𝒞`
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exfalso
      apply 𝒞.empty_not_mem
      have : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
      simpa [this] using 𝒞.univ_mem
    · exact h
  have hP := piV_closed_convex 𝒞 hV
  have h77 := eq_7_7 𝒞 hV
  -- `πV` is a fuzzy game without side payments
  have hF : IsNTUFuzzyGame (piV 𝒞 V) :=
    { subset_Rtau := fun τ hτ => (hP τ hτ).2.2.2.2.2
      nonempty := fun τ hτ => (hP τ hτ).2.2.2.2.1
      isClosed := fun τ hτ => (hP τ hτ).1
      convex := fun τ hτ => (hP τ hτ).2.1
      comprehensive := fun τ hτ => (hP τ hτ).2.2.1
      bddAbove := fun τ hτ => (hP τ hτ).2.2.2.1
      homogeneous := h77.1 }
  have hsup : Superadditive (piV 𝒞 V) := h77.2
  have hsub := core_piV_subset_core 𝒞 hV hbal
  have hcore := (theorem_5_1 hn hF hsup).1
  have h31 := theorem_3_1 hF
  have hcce := cce_eq_piV_cce 𝒞 hV hbal
  refine ⟨hcore.mono hsub, hcore, hsub, ?_, ?_⟩
  · rw [hcce.2]; exact h31.1
  · rw [hcce.1]; exact h31.2 hsup hn
