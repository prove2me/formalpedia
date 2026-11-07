-- Prove2me | solution 1 for FuzzyGames.NTUCore.core_piV_subset_core
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:44:53.125588+00:00
-- url     : https://prove2.me/submissions/ccce63b1-3250-431b-8a17-a63093c9182b

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
    (hV : IsNTUGame 𝒞 V) (hbal : V Finset.univ = piV 𝒞 V (coal Finset.univ)) :
    fuzzyCore (piV 𝒞 V) ⊆ ntuCore 𝒞 V := by
  classical
  rintro c ⟨hc, hcore⟩
  refine ⟨hbal ▸ hc, fun A hA hmem => ?_⟩
  have hcube : coal A ∈ cube n := by
    constructor <;> intro i <;> simp only [coal, Pi.zero_apply, Pi.one_apply] <;> split_ifs <;> norm_num
  have hne : coal A ≠ 0 := by
    have hAne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact 𝒞.empty_not_mem hA
    obtain ⟨i, hi⟩ := hAne
    intro h0
    have := congrFun h0 i
    simp [coal, hi] at this
  exact hcore (coal A) hcube hne
    (Set.sub_subset_sub (FuzzyGames.NTUCore.Aux.V_subset_piV 𝒞 hV A hA) le_rfl hmem)
