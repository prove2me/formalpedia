-- Prove2me | solution 1 for FuzzyGames.NTUCore.eq_7_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:43:47.626304+00:00
-- url     : https://prove2.me/submissions/05d02a8f-be4d-4882-b9ff-6f3e7c0776b6

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore.Aux
open FuzzyGames.NTUCore

theorem mem_piV {n : ℕ} (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ))
    (τ x : Fin n → ℝ) :
    x ∈ piV 𝒞 V τ ↔ ∃ m ∈ balances 𝒞 τ, ∃ w : Finset (Fin n) → Fin n → ℝ,
      (∀ A ∈ 𝒞.C, w A ∈ V A) ∧ ∑ A ∈ 𝒞.C, m A • w A = x := by
  classical
  unfold piV
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hx⟩
    rw [Set.mem_finsetSum] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have : ∀ A ∈ 𝒞.C, ∃ w ∈ V A, m A • w = g A := fun A hA => by
      simpa [Set.mem_smul_set] using hg hA
    choose! w hw hw' using this
    exact ⟨m, hm, w, hw, Finset.sum_congr rfl (fun A hA => hw' A hA)⟩
  · rintro ⟨m, hm, w, hw, rfl⟩
    exact ⟨m, hm, Set.finsetSum_mem_finsetSum _ _ _ (fun A hA =>
      Set.smul_mem_smul_set (hw A hA))⟩

theorem V_subset_piV {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) : ∀ A ∈ 𝒞.C, V A ⊆ piV 𝒞 V (coal A) := by
  classical
  intro A hA w hw
  rw [mem_piV]
  refine ⟨fun B => if B = A then 1 else 0, ⟨?_, ?_, ?_⟩,
    fun B => if h : B ∈ 𝒞.C ∧ B ≠ A then (hV.nonempty B h.1).some else w, ?_, ?_⟩
  · intro B; dsimp only; split_ifs <;> norm_num
  · intro B hB; dsimp only; rw [if_neg]; rintro rfl; exact hB hA
  · intro i
    dsimp only
    rw [Finset.sum_ite_eq']
    simp [coal, Finset.mem_filter, hA]
  · intro B hB
    show (if h : B ∈ 𝒞.C ∧ B ≠ A then (hV.nonempty B h.1).some else w) ∈ V B
    by_cases h : B ∈ 𝒞.C ∧ B ≠ A
    · rw [dif_pos h]; exact (hV.nonempty B h.1).some_mem
    · rw [dif_neg h]
      have : B = A := by by_contra h'; exact h ⟨hB, h'⟩
      subst this; exact hw
  · dsimp only
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' 𝒞.C A, if_pos hA]
    simp

end FuzzyGames.NTUCore.Aux

open FuzzyGames.NTUCore in
theorem solution {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    ∀ A ∈ 𝒞.C, V A ⊆ piV 𝒞 V (coal A) :=
  FuzzyGames.NTUCore.Aux.V_subset_piV 𝒞 hV
