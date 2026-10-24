-- Prove2me | solution 1 for Erdos624.zero_sum_count
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:41:14.973408+00:00
-- url     : https://prove2.me/submissions/1f84587e-9ac3-4cc0-9211-acfa11a40b3d

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624R5
open Finset

lemma zmod2_vec_add_self {m : ℕ} (x : Fin m → ZMod 2) : x + x = 0 := by
  funext j
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x j = z
  fin_cases z <;> rfl

/-- Zero-sum covering: `k` vectors in `𝔽₂^{k-1}` always have a nonempty zero-sum subfamily. -/
theorem zero_sum_covering (k : ℕ) (h : Fin (2 ^ k) → (Fin (k - 1) → ZMod 2))
    (Y : Finset (Fin (2 ^ k))) (hY : #Y = k) (hk : 1 ≤ k) :
    ∃ A ⊆ Y, A.Nonempty ∧ ∑ a ∈ A, h a = 0 := by
  have hc : (univ : Finset (Fin (k - 1) → ZMod 2)).card < Y.powerset.card := by
    rw [card_univ, card_powerset, hY]; simp [ZMod.card]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨A, hA, B, hB, hAB, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun A => ∑ a ∈ A, h a) (fun _ _ => mem_univ _)
  rw [mem_powerset] at hA hB
  refine ⟨symmDiff A B, ?_, ?_, ?_⟩
  · intro x hx; rw [mem_symmDiff] at hx
    rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact hA hx
    · exact hB hx
  · rw [nonempty_iff_ne_empty]; intro hc'; exact hAB (symmDiff_eq_bot.1 hc')
  · have h1 : ∑ a ∈ A, h a = ∑ a ∈ A \ B, h a + ∑ a ∈ A ∩ B, h a := by
      rw [← sum_sdiff (inter_subset_left : A ∩ B ⊆ A), sdiff_inter_self_left]
    have h2 : ∑ a ∈ B, h a = ∑ a ∈ B \ A, h a + ∑ a ∈ A ∩ B, h a := by
      rw [inter_comm, ← sum_sdiff (inter_subset_left : B ∩ A ⊆ B), sdiff_inter_self_left]
    have hs : ∑ a ∈ symmDiff A B, h a = ∑ a ∈ A \ B, h a + ∑ a ∈ B \ A, h a := by
      rw [symmDiff_def, sup_eq_union, sum_union disjoint_sdiff_sdiff]
    have he' : ∑ a ∈ A, h a = ∑ a ∈ B, h a := he
    rw [hs]
    have := zmod2_vec_add_self (∑ a ∈ A \ B, h a + ∑ a ∈ A ∩ B, h a)
    rw [← h1] at this
    rw [h1, h2] at he'
    calc ∑ a ∈ A \ B, h a + ∑ a ∈ B \ A, h a
        = (∑ a ∈ A \ B, h a + ∑ a ∈ A ∩ B, h a) + (∑ a ∈ B \ A, h a + ∑ a ∈ A ∩ B, h a) -
            (∑ a ∈ A ∩ B, h a + ∑ a ∈ A ∩ B, h a) := by abel
      _ = 0 := by rw [← he', ← h1, this, zmod2_vec_add_self, sub_zero]

/-- Exact zero-sum count (19): for nonempty `A`, `q · #{h : Σ_A h = 0} = #(U → 𝔽₂^m)`, `q = 2^m`. -/
theorem zero_sum_count {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ) (A : Finset U)
    (hA : A.Nonempty) :
    2 ^ m * #((univ : Finset (U → (Fin m → ZMod 2))).filter (fun h => ∑ a ∈ A, h a = 0)) =
      Fintype.card (U → (Fin m → ZMod 2)) := by
  obtain ⟨a0, ha0⟩ := hA
  set F : (Fin m → ZMod 2) → Finset (U → (Fin m → ZMod 2)) :=
    fun c => (univ : Finset (U → (Fin m → ZMod 2))).filter (fun h => ∑ a ∈ A, h a = c) with hF
  have hshift : ∀ c, #(F c) = #(F 0) := by
    intro c
    let e := Equiv.addRight (Pi.single a0 c : U → (Fin m → ZMod 2))
    have : F c = (F 0).map e.toEmbedding := by
      ext h
      rw [mem_map_equiv]
      simp only [hF, mem_filter, mem_univ, true_and]
      have he : e.symm h = h - Pi.single a0 c := by simp [e, sub_eq_add_neg]
      rw [he]
      simp only [Pi.sub_apply, sum_sub_distrib]
      rw [sum_pi_single' a0 c A, if_pos ha0, sub_eq_zero]
    rw [this, card_map]
  have hsum := card_eq_sum_card_fiberwise (s := (univ : Finset (U → (Fin m → ZMod 2))))
    (t := (univ : Finset (Fin m → ZMod 2))) (f := fun h => ∑ a ∈ A, h a) (fun _ _ => mem_univ _)
  rw [card_univ] at hsum
  rw [hsum, sum_congr rfl (fun c _ => hshift c), sum_const, card_univ, smul_eq_mul]
  simp [ZMod.card, hF]

end E624R5


namespace Erdos624

theorem zero_sum_count {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ) (A : Finset U)
    (hA : A.Nonempty) :
    2 ^ m * #((univ : Finset (U → (Fin m → ZMod 2))).filter (fun h => ∑ a ∈ A, h a = 0)) =
      Fintype.card (U → (Fin m → ZMod 2)) :=
  E624R5.zero_sum_count m A hA

end Erdos624

open Erdos624 in
theorem solution {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ) (A : Finset U)
    (hA : A.Nonempty) :
    2 ^ m * #((univ : Finset (U → (Fin m → ZMod 2))).filter (fun h => ∑ a ∈ A, h a = 0)) =
      Fintype.card (U → (Fin m → ZMod 2)) :=
  Erdos624.zero_sum_count m A hA

#print axioms solution
