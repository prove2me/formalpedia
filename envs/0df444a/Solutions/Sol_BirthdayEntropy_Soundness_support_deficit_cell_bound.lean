-- Prove2me | solution 1 for BirthdayEntropy.Soundness.support_deficit_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:19:46.601235+00:00
-- url     : https://prove2.me/submissions/1964a186-0d6c-4556-b47d-55190984bc24

import Definitions.Def_BirthdayEntropy_Soundness_Biclique
import Theorems.Thm_BirthdayEntropy_Soundness_binomial_product_deficit

noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness
namespace BirthdayEntropy.Soundness.Fixed

lemma card_signed {n ℓ : ℕ} (v : Vertex n ℓ) : (signed v).card = ℓ := by
  have hi : Function.Injective (fun i : v.1.val => (i.val,v.2 i)) := by
    intro a b h
    exact Subtype.ext (congrArg Prod.fst h)
  simp [signed,Finset.card_image_of_injective _ hi,v.1.property]

lemma support_signed {n ℓ : ℕ} (v : Vertex n ℓ) : support (signed v) = v.1.val := by
  ext i
  simp [support,signed]

lemma signed_inj {n ℓ : ℕ} : Function.Injective (@signed n ℓ) := by
  intro v w h
  have hS : v.1 = w.1 := Subtype.ext (by simpa only [support_signed] using congrArg support h)
  cases v with
  | mk S a =>
    cases w with
    | mk T b =>
      dsimp only at hS
      subst T
      congr 1
      funext i
      have hm : (i.val,a i) ∈ signed (⟨S,a⟩ : Vertex n ℓ) := by
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rw [h] at hm
      obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hm
      have hji : j = i := Subtype.ext (congrArg Prod.fst heq)
      subst j
      exact (congrArg Prod.snd heq).symm

def allowed {n ℓ : ℕ} (A : Finset (Signed n)) : Finset (Vertex n ℓ) :=
  Finset.univ.filter (fun v => signed v ⊆ A)

lemma allowed_card {n ℓ : ℕ} (A : Finset (Signed n)) :
    (allowed (ℓ := ℓ) A).card ≤ Nat.choose A.card ℓ := by
  have hmap : (allowed (ℓ := ℓ) A).image signed ⊆ A.powersetCard ℓ := by
    intro S hS
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp hv).2,card_signed v⟩
  have h := Finset.card_le_card hmap
  simpa [Finset.card_image_of_injective _ signed_inj] using h

lemma flatten_contains_left {n ℓ r : ℕ} (X : Tuple n ℓ r) (i : Fin r) :
    signed (X.1 i) ⊆ (flatten X).1 := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩

lemma flatten_contains_right {n ℓ r : ℕ} (X : Tuple n ℓ r) (j : Fin r) :
    signed (X.2 j) ⊆ (flatten X).2 := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hp⟩

lemma accepted_cell_count {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (r : ℕ) (F : Flattening n) :
    (acceptedCell φ H r F).card ≤ ((allowed (ℓ := ℓ) F.1).card)^r * ((allowed (ℓ := ℓ) F.2).card)^r := by
  have hsub : acceptedCell φ H r F ⊆
      (Fintype.piFinset (fun _ : Fin r => allowed F.1)) ×ˢ (Fintype.piFinset (fun _ : Fin r => allowed F.2)) := by
    intro X hX
    have hh : X ∈ accepted φ H r ∧ flatten X = F := by simpa only [acceptedCell,cell,Finset.mem_filter] using hX
    have hF := hh.2
    apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      simp only [allowed,Finset.mem_filter,Finset.mem_univ,true_and]
      simpa only [hF] using flatten_contains_left X i
    · apply Fintype.mem_piFinset.mpr
      intro j
      simp only [allowed,Finset.mem_filter,Finset.mem_univ,true_and]
      simpa only [hF] using flatten_contains_right X j
  simpa using Finset.card_le_card hsub

private lemma signed_card_sum {n : ℕ} (A : Finset (Signed n)) :
    (A.card : ℝ) = ∑ i : Fin n, ((if (i,false) ∈ A then (1:ℝ) else 0) + (if (i,true) ∈ A then (1:ℝ) else 0)) := by
  calc
    _ = ∑ p : Signed n, if p ∈ A then (1:ℝ) else 0 := by simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma support_deficit {n : ℕ} (F : Flattening n) (h : CrossConsistent F) :
    (F.1.card : ℝ) + F.2.card + (terrible F).card ≤ 2*n := by
  rw [signed_card_sum,signed_card_sum]
  have ht : ((terrible F).card : ℝ) = ∑ i : Fin n, if i ∈ terrible F then (1:ℝ) else 0 := by simp
  rw [ht,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : Fin n, (2:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h0 := h i false
      have h1 := h i true
      simp only [Bool.not_false,Bool.not_true] at h0 h1
      by_cases a0 : (i,false) ∈ F.1 <;> by_cases a1 : (i,true) ∈ F.1 <;>
        by_cases b0 : (i,false) ∈ F.2 <;> by_cases b1 : (i,true) ∈ F.2 <;>
        simp_all [terrible,badLeft,badRight,good,Bool.exists_bool] <;> norm_num
    _ = _ := by simp [mul_comm]
end BirthdayEntropy.Soundness.Fixed

noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness

theorem solution {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (r : ℕ) (F : Flattening n) (hF : CrossConsistent F) (hℓn : ℓ ≤ n) :
    ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
      Real.exp (-(r : ℝ) * ratio n ℓ * (terrible F).card) := by
  classical
  have hc : ((acceptedCell φ H r F).card : ℝ) ≤
      ((Fixed.allowed (ℓ := ℓ) F.1).card : ℝ)^r * ((Fixed.allowed (ℓ := ℓ) F.2).card : ℝ)^r := by
    exact_mod_cast Fixed.accepted_cell_count φ H r F
  have ha : ((Fixed.allowed (ℓ := ℓ) F.1).card : ℝ) ≤ Nat.choose F.1.card ℓ := by exact_mod_cast Fixed.allowed_card F.1
  have hb : ((Fixed.allowed (ℓ := ℓ) F.2).card : ℝ) ≤ Nat.choose F.2.card ℓ := by exact_mod_cast Fixed.allowed_card F.2
  by_cases hr : r = 0
  · subst r
    simpa using hc
  have hrp : 0 < r := Nat.pos_of_ne_zero hr
  have hc' : ((acceptedCell φ H r F).card : ℝ) ≤
      (Nat.choose F.1.card ℓ : ℝ)^r * (Nat.choose F.2.card ℓ : ℝ)^r := by
    apply hc.trans
    gcongr
  by_cases hla : ℓ ≤ F.1.card
  swap
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hla),Nat.cast_zero,zero_pow hr,zero_mul] at hc'
    exact hc'.trans (by positivity)
  by_cases hlb : ℓ ≤ F.2.card
  swap
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hlb),Nat.cast_zero,zero_pow hr,mul_zero] at hc'
    exact hc'.trans (by positivity)
  have hbin := binomial_product_deficit F.1.card F.2.card n ℓ ((terrible F).card : ℝ)
    (by positivity) hla hlb hℓn (Fixed.support_deficit F hF)
  have hp := pow_le_pow_left₀ (show (0:ℝ) ≤ (Nat.choose F.1.card ℓ : ℝ) * (Nat.choose F.2.card ℓ : ℝ) by positivity) hbin r
  rw [mul_pow] at hp
  apply hc'.trans
  apply hp.trans_eq
  rw [mul_pow,←pow_mul,show 2*r=r*2 by omega,←Real.exp_nat_mul]
  congr 2
  unfold ratio
  ring