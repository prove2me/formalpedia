-- Prove2me | solution 1 for Dubner.pandey_proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T11:50:29.968371+00:00
-- url     : https://prove2.me/submissions/b2813a03-2277-4b66-bec8-14a8f2095a5d

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

open Dubner

namespace DubnerPandey

/-- A Chebyshev-type bound, from `primorial x ≤ 4 ^ x`: among the primes up to `x`, at most `x / s`
are larger than `4 ^ s`. -/
theorem mul_card_large_primes_le (s x : ℕ) :
    s * (((Finset.range (x + 1)).filter Nat.Prime).filter (fun p => 4 ^ s < p)).card ≤ x := by
  set P := (Finset.range (x + 1)).filter Nat.Prime with hP
  set Q := P.filter (fun p => 4 ^ s < p) with hQ
  have h1 : (4 ^ s) ^ Q.card ≤ ∏ p ∈ Q, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun p hp => (Finset.mem_filter.mp hp).2.le)
  have h2 : ∏ p ∈ Q, p ≤ ∏ p ∈ P, p := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not P (fun p => 4 ^ s < p) (fun p => p)
    have hpos : 0 < ∏ p ∈ P.filter (fun p => ¬ 4 ^ s < p), p :=
      Finset.prod_pos (fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos)
    calc ∏ p ∈ Q, p ≤ (∏ p ∈ Q, p) * ∏ p ∈ P.filter (fun p => ¬ 4 ^ s < p), p :=
          Nat.le_mul_of_pos_right _ hpos
      _ = ∏ p ∈ P, p := hsplit
  have h3 : ∏ p ∈ P, p ≤ 4 ^ x := primorial_le_four_pow x
  have h4 : 4 ^ (s * Q.card) ≤ 4 ^ x := by
    rw [pow_mul]
    exact h1.trans (h2.trans h3)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4

/-- The number of primes up to `x` is at most `4 ^ s + 1` plus the number of those above `4 ^ s`. -/
theorem card_primes_le (s x : ℕ) :
    ((Finset.range (x + 1)).filter Nat.Prime).card ≤
      4 ^ s + 1 + (((Finset.range (x + 1)).filter Nat.Prime).filter (fun p => 4 ^ s < p)).card := by
  set P := (Finset.range (x + 1)).filter Nat.Prime with hP
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun p => 4 ^ s < p)
  have hsmall : (P.filter (fun p => ¬ 4 ^ s < p)).card ≤ 4 ^ s + 1 := by
    have hsub : P.filter (fun p => ¬ 4 ^ s < p) ⊆ Finset.range (4 ^ s + 1) := by
      intro p hp
      have := (Finset.mem_filter.mp hp).2
      exact Finset.mem_range.mpr (by omega)
    simpa using Finset.card_le_card hsub
  omega

/-- First part of Pandey's Proposition 1. -/
theorem part1 (A : Set ℕ) (_hA_even : ∀ n ∈ A, Even n)
    (hdens : ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x → c * x ≤ (A ∩ Set.Iic x).ncard)
    (hS : ∀ n ∈ A, ∃ p t : ℕ, Nat.Prime p ∧ IsTPrime t ∧ n = p + t) :
    {t : ℕ | IsTPrime t}.Infinite := by
  intro hfin
  obtain ⟨c, hc, X, hX⟩ := hdens
  set T := hfin.toFinset with hT
  set k := T.card with hk
  -- a natural number `s ≥ 1` with `2 k ≤ c s`
  obtain ⟨s, hs1, hs⟩ : ∃ s : ℕ, 1 ≤ s ∧ 2 * (k : ℝ) ≤ c * s := by
    refine ⟨⌈2 * (k : ℝ) / c⌉₊ + 1, by omega, ?_⟩
    have h := Nat.le_ceil (2 * (k : ℝ) / c)
    have h' : 2 * (k : ℝ) / c ≤ ((⌈2 * (k : ℝ) / c⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    rw [div_le_iff₀ hc] at h'
    linarith
  -- every element of `A` up to `x` is `p + t` with `p ≤ x` prime and `t ∈ T`
  have hcount : ∀ x : ℕ, ∃ q : ℕ,
      (A ∩ Set.Iic x).ncard ≤ k * (4 ^ s + 1 + q) ∧ s * q ≤ x := by
    intro x
    set P := (Finset.range (x + 1)).filter Nat.Prime with hP
    have hsub : A ∩ Set.Iic x ⊆ ↑((P ×ˢ T).image (fun pt : ℕ × ℕ => pt.1 + pt.2)) := by
      rintro n ⟨hnA, hnx⟩
      obtain ⟨p, t, hp, ht, rfl⟩ := hS n hnA
      have hpx : p + t ≤ x := hnx
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(p, t), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
      · exact hfin.mem_toFinset.mpr ht
    have h1 : (A ∩ Set.Iic x).ncard ≤ ((P ×ˢ T).image (fun pt : ℕ × ℕ => pt.1 + pt.2)).card := by
      have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rwa [Set.ncard_coe_finset] at h
    have h2 : ((P ×ˢ T).image (fun pt : ℕ × ℕ => pt.1 + pt.2)).card ≤ P.card * k := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
    have h3 := card_primes_le s x
    refine ⟨(P.filter (fun p => 4 ^ s < p)).card, ?_, mul_card_large_primes_le s x⟩
    calc (A ∩ Set.Iic x).ncard ≤ P.card * k := h1.trans h2
      _ ≤ (4 ^ s + 1 + (P.filter (fun p => 4 ^ s < p)).card) * k := Nat.mul_le_mul_right k h3
      _ = k * (4 ^ s + 1 + (P.filter (fun p => 4 ^ s < p)).card) := Nat.mul_comm _ _
  -- a large `x` contradicts the density hypothesis
  set M : ℝ := (k : ℝ) * ((4 : ℝ) ^ s + 1) with hM
  set x := max X (⌈2 * M / c⌉₊ + 1) with hx
  obtain ⟨q, hq1, hq2⟩ := hcount x
  have hxlarge : 2 * M < c * x := by
    have h := Nat.le_ceil (2 * M / c)
    have hle : ((⌈2 * M / c⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast le_max_right X (⌈2 * M / c⌉₊ + 1)
    have hlt : 2 * M / c < (x : ℝ) := by
      push_cast at hle
      linarith
    rw [div_lt_iff₀ hc] at hlt
    linarith
  have hdens := hX x (le_max_left _ _)
  have hq1' : ((A ∩ Set.Iic x).ncard : ℝ) ≤ M + k * q := by
    have h : ((A ∩ Set.Iic x).ncard : ℝ) ≤ ((k * (4 ^ s + 1 + q) : ℕ) : ℝ) := by exact_mod_cast hq1
    push_cast at h
    rw [hM]
    linarith
  have hq2' : (s : ℝ) * q ≤ x := by exact_mod_cast hq2
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  -- `s (c x) ≤ s M + k x` and `2 k x ≤ c s x`
  have hA : (s : ℝ) * (c * x) ≤ s * M + k * x := by
    have h5 : c * x ≤ M + k * q := hdens.trans hq1'
    have h6 : (s : ℝ) * (c * x) ≤ s * (M + k * q) := mul_le_mul_of_nonneg_left h5 hs0.le
    have h7 : (k : ℝ) * (s * q) ≤ k * x := mul_le_mul_of_nonneg_left hq2' hk0
    nlinarith
  have hB : 2 * (k : ℝ) * x ≤ c * s * x := mul_le_mul_of_nonneg_right hs hx0
  have hC : (s : ℝ) * (2 * M) < s * (c * x) := mul_lt_mul_of_pos_left hxlarge hs0
  nlinarith

/-- Infinitely many t-primes give infinitely many twin prime pairs. -/
theorem twin_infinite_of_tprime_infinite (h : {t : ℕ | IsTPrime t}.Infinite) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  intro hfin
  apply h
  refine (hfin.union (hfin.image (fun p => p + 2))).subset ?_
  rintro t ⟨htp, h2 | h2⟩
  · right
    have ht2 : 2 ≤ t := htp.two_le
    have he : t - 2 + 2 = t := by omega
    refine ⟨t - 2, ⟨h2, ?_⟩, he⟩
    rw [he]
    exact htp
  · left
    exact ⟨htp, h2⟩

/-- The even numbers from `6` on have positive lower density: at least `x / 4` of them are `≤ x`
as soon as `x ≥ 12`. -/
theorem evens_dense : ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    c * x ≤ ({n : ℕ | 6 ≤ n ∧ Even n} ∩ Set.Iic x).ncard := by
  refine ⟨1 / 4, by norm_num, 12, fun x hx => ?_⟩
  set F := (Finset.range ((x - 4) / 2)).image (fun i => 2 * i + 6) with hF
  have hsub : (↑F : Set ℕ) ⊆ {n : ℕ | 6 ≤ n ∧ Even n} ∩ Set.Iic x := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hn)
    have hi' := Finset.mem_range.mp hi
    refine ⟨⟨by omega, ⟨i + 3, by omega⟩⟩, ?_⟩
    show 2 * i + 6 ≤ x
    omega
  have hcard : F.card = (x - 4) / 2 := by
    rw [hF, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
  have hfin : ({n : ℕ | 6 ≤ n ∧ Even n} ∩ Set.Iic x).Finite :=
    (Set.finite_Iic x).subset Set.inter_subset_right
  have h1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, hcard] at h1
  have h2 : x ≤ 4 * ({n : ℕ | 6 ≤ n ∧ Even n} ∩ Set.Iic x).ncard := by omega
  have h3 : (x : ℝ) ≤ 4 * (({n : ℕ | 6 ≤ n ∧ Even n} ∩ Set.Iic x).ncard : ℝ) := by
    exact_mod_cast h2
  linarith

end DubnerPandey

open DubnerPandey in
/-- Pandey's Proposition 1.

Part 1: if a set of even numbers of positive lower density consists of sums of a prime and a
t-prime, then there are infinitely many t-primes. Part 2: statement (S) implies Goldbach's
conjecture and the twin prime conjecture. -/
theorem solution :
    (∀ A : Set ℕ, (∀ n ∈ A, Even n) →
        (∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x → c * x ≤ (A ∩ Set.Iic x).ncard) →
        (∀ n ∈ A, ∃ p t : ℕ, Nat.Prime p ∧ IsTPrime t ∧ n = p + t) →
        {t : ℕ | IsTPrime t}.Infinite) ∧
    ((∀ n : ℕ, 6 ≤ n → Even n → ∃ p t : ℕ, Nat.Prime p ∧ IsTPrime t ∧ n = p + t) →
        (∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) ∧
          {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite) := by
  refine ⟨part1, fun hS => ⟨?_, ?_⟩⟩
  · intro n hn4 hne
    by_cases h6 : 6 ≤ n
    · obtain ⟨p, t, hp, ht, hpt⟩ := hS n h6 hne
      exact ⟨p, t, hp, ht.1, hpt⟩
    · obtain ⟨j, hj⟩ := hne
      exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by omega⟩
  · apply twin_infinite_of_tprime_infinite
    exact part1 {n : ℕ | 6 ≤ n ∧ Even n} (fun n hn => hn.2) evens_dense
      (fun n hn => hS n hn.1 hn.2)
