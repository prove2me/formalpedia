-- Prove2me | solution 1 for FuzzyGames.NTUCore.cce_eq_piV_cce
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:44:53.882874+00:00
-- url     : https://prove2.me/submissions/ba71f916-efe0-4a76-8610-cd34197d25b1

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


theorem sum_A_eq_sum {n : ℕ} (A : Finset (Fin n)) (l w : Fin n → ℝ) (hw : w ∈ Rtau (coal A)) :
    ∑ i ∈ A, l i * w i = ∑ i, l i * w i := by
  classical
  apply Finset.sum_subset (Finset.subset_univ A)
  intro i _ hi
  have : w i = 0 := hw i (by simp [coal, hi])
  simp [this]

theorem sum_swap {n : ℕ} (𝒞 : CoalFamily n) (m : Finset (Fin n) → ℝ) (f : Fin n → ℝ) :
    ∑ A ∈ 𝒞.C, m A * ∑ i ∈ A, f i = ∑ i, f i * ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A := by
  classical
  have h1 : ∀ A ∈ 𝒞.C, m A * ∑ i ∈ A, f i = ∑ i, if i ∈ A then m A * f i else 0 := by
    intro A _
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1; ext i; simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> ring

theorem cce_iff {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (l c : Fin n → ℝ) :
    (∀ A ∈ 𝒞.C, coalSupport V A l ≤ ((∑ i ∈ A, l i * c i : ℝ) : EReal)) ↔
      (∀ τ ∈ cube n, supportFn (piV 𝒞 V τ) l ≤ ((∑ i, l i * τ i * c i : ℝ) : EReal)) := by
  classical
  constructor
  · intro h τ _
    unfold supportFn
    refine iSup₂_le fun x hx => ?_
    obtain ⟨m, ⟨hm0, _, hmτ⟩, w, hw, rfl⟩ := (mem_piV 𝒞 V τ x).1 hx
    rw [EReal.coe_le_coe_iff]
    have key : ∀ A ∈ 𝒞.C, ∑ i, l i * w A i ≤ ∑ i ∈ A, l i * c i := by
      intro A hA
      rw [← sum_A_eq_sum A l (w A) (hV.subset_Rtau A hA (hw A hA))]
      have h1 : ((∑ i ∈ A, l i * w A i : ℝ) : EReal) ≤ coalSupport V A l := by
        unfold coalSupport
        exact le_iSup₂ (f := fun c (_ : c ∈ V A) => ((∑ i ∈ A, l i * c i : ℝ) : EReal)) (w A) (hw A hA)
      exact EReal.coe_le_coe_iff.1 (h1.trans (h A hA))
    calc ∑ i, l i * (∑ A ∈ 𝒞.C, m A • w A) i
        = ∑ A ∈ 𝒞.C, m A * ∑ i, l i * w A i := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro A _; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ ∑ A ∈ 𝒞.C, m A * ∑ i ∈ A, l i * c i := by
          apply Finset.sum_le_sum; intro A hA
          exact mul_le_mul_of_nonneg_left (key A hA) (hm0 A)
      _ = ∑ i, l i * c i * ∑ A ∈ 𝒞.C.filter (fun A => i ∈ A), m A := sum_swap 𝒞 m _
      _ = ∑ i, l i * τ i * c i := by
          apply Finset.sum_congr rfl; intro i _; rw [hmτ i]; ring
  · intro h A hA
    unfold coalSupport
    refine iSup₂_le fun w hw => ?_
    have hcube : coal A ∈ cube n := by
      constructor <;> intro i <;> simp only [coal, Pi.zero_apply, Pi.one_apply] <;> split_ifs <;> norm_num
    have h1 := h (coal A) hcube
    have h2 : ((∑ i, l i * w i : ℝ) : EReal) ≤ supportFn (piV 𝒞 V (coal A)) l := by
      unfold supportFn
      exact le_iSup₂ (f := fun c (_ : c ∈ piV 𝒞 V (coal A)) => ((∑ i, l i * c i : ℝ) : EReal)) w
        (V_subset_piV 𝒞 hV A hA hw)
    rw [sum_A_eq_sum A l w (hV.subset_Rtau A hA hw)]
    refine (h2.trans h1).trans (le_of_eq ?_)
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ A)]
    · apply Finset.sum_congr rfl; intro i hi; simp [coal, hi]
    · intro i _ hi; simp [coal, hi]

end FuzzyGames.NTUCore.Aux

open FuzzyGames.NTUCore in
theorem solution {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (hbal : IsBalanced 𝒞 V) :
    ntuWeakCCE 𝒞 V = weakCCE (piV 𝒞 V) ∧ ntuStrongCCE 𝒞 V = strongCCE (piV 𝒞 V) := by
  unfold IsBalanced at hbal
  constructor
  · ext c
    simp only [ntuWeakCCE, weakCCE, Set.mem_setOf_eq, hbal]
    constructor
    · rintro ⟨h1, l, hl, h2⟩; exact ⟨h1, l, hl, (FuzzyGames.NTUCore.Aux.cce_iff 𝒞 hV l c).1 h2⟩
    · rintro ⟨h1, l, hl, h2⟩; exact ⟨h1, l, hl, (FuzzyGames.NTUCore.Aux.cce_iff 𝒞 hV l c).2 h2⟩
  · ext c
    simp only [ntuStrongCCE, strongCCE, Set.mem_setOf_eq, hbal]
    constructor
    · rintro ⟨h1, l, hl, h2⟩; exact ⟨h1, l, hl, (FuzzyGames.NTUCore.Aux.cce_iff 𝒞 hV l c).1 h2⟩
    · rintro ⟨h1, l, hl, h2⟩; exact ⟨h1, l, hl, (FuzzyGames.NTUCore.Aux.cce_iff 𝒞 hV l c).2 h2⟩
