-- Prove2me | solution 1 for EssentialCodingTheory.generalized_hamming_bound
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-14T19:40:23.581599+00:00
-- url     : https://prove2.me/submissions/70ff0f4f-c226-4495-8c6b-f40f7158367d

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Finset

namespace EssentialCodingTheory

open Polynomial in
lemma hamming_poly {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (c : Fin n → α) :
    (∑ x : Fin n → α, (X : ℕ[X]) ^ hammingDist c x)
      = (C ((Fintype.card α - 1 : ℕ)) * X + 1) ^ n := by
  have h1 : ∀ x : Fin n → α, (X : ℕ[X]) ^ hammingDist c x
      = ∏ j, (if c j ≠ x j then (X : ℕ[X]) else 1) := by
    intro x
    rw [hammingDist, Finset.card_filter, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j a => if c j ≠ a then (X : ℕ[X]) else 1)]
  have h2 : ∀ j : Fin n, (∑ a : α, if c j ≠ a then (X : ℕ[X]) else 1)
      = C ((Fintype.card α - 1 : ℕ)) * X + 1 := by
    intro j
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have hne : (univ.filter fun a => c j ≠ a).card = Fintype.card α - 1 := by
      rw [Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
    have heq : (univ.filter fun a => ¬ c j ≠ a).card = 1 := by
      simp only [not_not]
      rw [Finset.filter_eq]
      simp
    rw [hne, heq, one_smul, nsmul_eq_mul]
    rfl
  rw [Finset.prod_congr rfl fun j _ => h2 j, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

open Polynomial in
lemma hamming_sphere_card {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (c : Fin n → α) (i : ℕ) :
    (univ.filter fun x : Fin n → α => hammingDist c x = i).card
      = n.choose i * (Fintype.card α - 1) ^ i := by
  have hc := congrArg (fun p : ℕ[X] => p.coeff i) (hamming_poly c)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at hc
  rw [Finset.card_filter]
  have : (∑ x : Fin n → α, if i = hammingDist c x then 1 else 0)
      = ∑ x : Fin n → α, if hammingDist c x = i then 1 else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [eq_comm]
  rw [← this, hc, add_pow, Polynomial.finsetSum_coeff]
  simp only [one_pow, mul_one, mul_pow, ← Polynomial.C_pow]
  have : ∀ m ∈ range (n + 1),
      (C ((Fintype.card α - 1 : ℕ) ^ m) * X ^ m * (n.choose m : ℕ[X])).coeff i
        = if i = m then n.choose i * (Fintype.card α - 1) ^ i else 0 := by
    intro m _
    rw [← Polynomial.C_eq_natCast, mul_comm, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; rw [Nat.cast_id, mul_comm]
    · rfl
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp only [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]

lemma hamming_ball_card {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (c : Fin n → α) (t : ℕ) :
    (univ.filter fun x : Fin n → α => hammingDist c x ≤ t).card
      = ∑ i ∈ range (t + 1), n.choose i * (Fintype.card α - 1) ^ i := by
  simp_rw [← hamming_sphere_card c, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem generalized_hamming_bound {α : Type*} [Fintype α] [DecidableEq α] {n d : ℕ}
    (C : Finset (Fin n → α))
    (hC : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    Real.logb (Fintype.card α) C.card ≤
      n - Real.logb (Fintype.card α)
        ((∑ i ∈ range ((d - 1) / 2 + 1), n.choose i * (Fintype.card α - 1) ^ i : ℕ) : ℝ) := by
  set q := Fintype.card α with hq
  set t := (d - 1) / 2 with ht
  set V := ∑ i ∈ range (t + 1), n.choose i * (q - 1) ^ i with hV
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have hl : Real.log (q : ℝ) = 0 := by
      rcases (by omega : q = 0 ∨ q = 1) with h | h <;> simp [h]
    simp only [Real.logb, hl, div_zero, sub_zero]
    positivity
  · -- balls
    set B : (Fin n → α) → Finset (Fin n → α) :=
      fun c => univ.filter fun x => hammingDist c x ≤ t with hB
    have hBcard : ∀ c, (B c).card = V := fun c => hamming_ball_card c t
    have hdisj : (C : Set (Fin n → α)).PairwiseDisjoint B := by
      intro c₁ h₁ c₂ h₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx1 hx2
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      have htri := hammingDist_triangle c₁ x c₂
      rw [hammingDist_comm x c₂] at htri
      have hd := hC c₁ h₁ c₂ h₂ hne
      have hpos : hammingDist c₁ c₂ ≠ 0 := hammingDist_ne_zero.mpr hne
      omega
    have hmain : C.card * V ≤ q ^ n := by
      have h := Finset.card_biUnion hdisj
      rw [Finset.sum_congr rfl fun c _ => hBcard c, Finset.sum_const, smul_eq_mul] at h
      rw [← h]
      calc (C.biUnion B).card ≤ (univ : Finset (Fin n → α)).card := card_le_univ _
        _ = q ^ n := by simp [hq]
    have hne : Nonempty α := by
      rw [← Fintype.card_pos_iff]; omega
    have hVle : V ≤ q ^ n := by
      obtain ⟨a⟩ := hne
      rw [← hBcard (fun _ => a)]
      calc (B fun _ => a).card ≤ (univ : Finset (Fin n → α)).card := card_le_univ _
        _ = q ^ n := by simp [hq]
    have hV1 : 1 ≤ V := by
      rw [hV, Finset.sum_range_succ']
      simp
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq2
    have hVR : (0 : ℝ) < V := by exact_mod_cast hV1
    have hn : Real.logb q ((q : ℝ) ^ n) = n := by
      rw [Real.logb_pow, Real.logb_self_eq_one hqR, mul_one]
    rcases Nat.eq_zero_or_pos C.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.logb_zero, sub_nonneg, ← hn]
      apply Real.logb_le_logb_of_le hqR hVR
      exact_mod_cast hVle
    · have hCR : (0 : ℝ) < C.card := by exact_mod_cast h0
      rw [le_sub_iff_add_le, ← Real.logb_mul hCR.ne' hVR.ne', ← hn]
      apply Real.logb_le_logb_of_le hqR (mul_pos hCR hVR)
      exact_mod_cast hmain

end EssentialCodingTheory


-- Platform entry point: restates the target verbatim.
namespace EssentialCodingTheory
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α] {n d : ℕ}
    (C : Finset (Fin n → α))
    (hC : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    Real.logb (Fintype.card α) C.card ≤
      n - Real.logb (Fintype.card α)
        ((∑ i ∈ range ((d - 1) / 2 + 1), n.choose i * (Fintype.card α - 1) ^ i : ℕ) : ℝ) := by
  apply @EssentialCodingTheory.generalized_hamming_bound <;> assumption
end EssentialCodingTheory
