-- Prove2me | solution 1 for ConstrNestedLogit.Card.knapsack_optimal_order_sign
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:18:06.378594+00:00
-- url     : https://prove2.me/submissions/a19e27e8-b2ea-4d39-a898-ab8be4e6d913

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Card_Knapsack

set_option autoImplicit false

open NestedLogitVariants.LP ConstrNestedLogit.Card

lemma cnc_suff {n : ℕ} (f : Fin n → ℝ) (C : ℕ) (S : Finset (Fin n)) (hcard : S.card ≤ C)
    (hpos : ∀ j ∈ S, 0 ≤ f j)
    (horder : ∀ j ∈ S, ∀ k ∉ S, f k ≤ f j)
    (hrest : S.card < C → ∀ k ∉ S, f k ≤ 0) :
    ∀ S' : Finset (Fin n), S'.card ≤ C → ∑ j ∈ S', f j ≤ ∑ j ∈ S, f j := by
  intro S' hS'
  have e1 : ∑ j ∈ S', f j = ∑ j ∈ S' ∩ S, f j + ∑ j ∈ S' \ S, f j :=
    (Finset.sum_inter_add_sum_sdiff S' S f).symm
  have e2 : ∑ j ∈ S, f j = ∑ j ∈ S ∩ S', f j + ∑ j ∈ S \ S', f j :=
    (Finset.sum_inter_add_sum_sdiff S S' f).symm
  rw [Finset.inter_comm S S'] at e2
  suffices h : ∑ j ∈ S' \ S, f j ≤ ∑ j ∈ S \ S', f j by linarith
  have hSpos : 0 ≤ ∑ j ∈ S \ S', f j :=
    Finset.sum_nonneg (fun j hj => hpos j (Finset.mem_sdiff.1 hj).1)
  by_cases hlt : S.card < C
  · have : ∑ j ∈ S' \ S, f j ≤ 0 :=
      Finset.sum_nonpos (fun k hk => hrest hlt k (Finset.mem_sdiff.1 hk).2)
    linarith
  · have hceq : S.card = C := le_antisymm hcard (not_lt.1 hlt)
    have c1 := Finset.card_sdiff_add_card_inter S' S
    have c2 := Finset.card_sdiff_add_card_inter S S'
    rw [Finset.inter_comm S S'] at c2
    have hcc : (S' \ S).card ≤ (S \ S').card := by omega
    rcases (S' \ S).eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using hSpos
    · have hne2 : (S \ S').Nonempty := by
        rw [← Finset.card_pos] at hne ⊢; omega
      obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (S \ S') f hne2
      have hj0S : j0 ∈ S := (Finset.mem_sdiff.1 hj0).1
      have hj0pos : 0 ≤ f j0 := hpos j0 hj0S
      have h1 : ∑ j ∈ S' \ S, f j ≤ (S' \ S).card • f j0 :=
        Finset.sum_le_card_nsmul _ _ _ (fun k hk => horder j0 hj0S k (Finset.mem_sdiff.1 hk).2)
      have h2 : (S' \ S).card • f j0 ≤ (S \ S').card • f j0 :=
        nsmul_le_nsmul_left hj0pos hcc
      have h3 : (S \ S').card • f j0 ≤ ∑ j ∈ S \ S', f j :=
        Finset.card_nsmul_le_sum _ _ _ hmin
      linarith

lemma cnc_nec {n : ℕ} (f : Fin n → ℝ) (C : ℕ) (S : Finset (Fin n)) (hcard : S.card ≤ C)
    (hopt : ∀ S' : Finset (Fin n), S'.card ≤ C → ∑ j ∈ S', f j ≤ ∑ j ∈ S, f j) :
    (∀ j ∈ S, 0 ≤ f j) ∧ (∀ j ∈ S, ∀ k ∉ S, f k ≤ f j) ∧
      (S.card < C → ∀ k ∉ S, f k ≤ 0) := by
  classical
  refine ⟨fun j hj => ?_, fun j hj k hk => ?_, fun hlt k hk => ?_⟩
  · by_contra hneg
    push_neg at hneg
    have h := hopt (S.erase j) ((Finset.card_erase_le).trans hcard)
    have := Finset.add_sum_erase S f hj
    linarith
  · by_contra hneg
    push_neg at hneg
    have hkS : k ∉ S.erase j := fun h => hk (Finset.mem_of_mem_erase h)
    have hc : (insert k (S.erase j)).card ≤ C := by
      rw [Finset.card_insert_of_notMem hkS, Finset.card_erase_of_mem hj]
      have : 0 < S.card := Finset.card_pos.2 ⟨j, hj⟩
      omega
    have h := hopt _ hc
    rw [Finset.sum_insert hkS] at h
    have := Finset.add_sum_erase S f hj
    linarith
  · by_contra hneg
    push_neg at hneg
    have h := hopt (insert k S) (by rw [Finset.card_insert_of_notMem hk]; omega)
    rw [Finset.sum_insert hk] at h
    linarith

theorem solution {ι : Type*} {n : ℕ} (I : Instance ι n) (c : ι → ℕ) (i : ι)
    (u u' : ℝ)
    (horder : ∀ j k : Fin n, utility I i j u ≤ utility I i k u ↔ utility I i j u' ≤ utility I i k u')
    (hsign : ∀ j : Fin n, SignType.sign (utility I i j u) = SignType.sign (utility I i j u'))
    (S : Finset (Fin n)) :
    IsKnapsackOptimal I c i u S ↔ IsKnapsackOptimal I c i u' S := by
  have h0 : ∀ j : Fin n, (0 ≤ utility I i j u ↔ 0 ≤ utility I i j u') := by
    intro j
    rw [← sign_nonneg_iff, ← sign_nonneg_iff (a := utility I i j u'), hsign j]
  have h0' : ∀ j : Fin n, (utility I i j u ≤ 0 ↔ utility I i j u' ≤ 0) := by
    intro j
    rw [← sign_nonpos_iff, ← sign_nonpos_iff (a := utility I i j u'), hsign j]
  -- general equivalence for one parameter, then transfer
  have key : ∀ (v : ℝ), IsKnapsackOptimal I c i v S ↔
      (S.card ≤ c i ∧ (∀ j ∈ S, 0 ≤ utility I i j v) ∧
        (∀ j ∈ S, ∀ k ∉ S, utility I i k v ≤ utility I i j v) ∧
        (S.card < c i → ∀ k ∉ S, utility I i k v ≤ 0)) := by
    intro v
    constructor
    · rintro ⟨hcard, hopt⟩
      obtain ⟨a, b, d⟩ := cnc_nec (fun j => utility I i j v) (c i) S hcard hopt
      exact ⟨hcard, a, b, d⟩
    · rintro ⟨hcard, a, b, d⟩
      exact ⟨hcard, cnc_suff (fun j => utility I i j v) (c i) S hcard a b d⟩
  rw [key u, key u']
  constructor
  · rintro ⟨hc, a, b, d⟩
    exact ⟨hc, fun j hj => (h0 j).1 (a j hj), fun j hj k hk => (horder k j).1 (b j hj k hk),
      fun hlt k hk => (h0' k).1 (d hlt k hk)⟩
  · rintro ⟨hc, a, b, d⟩
    exact ⟨hc, fun j hj => (h0 j).2 (a j hj), fun j hj k hk => (horder k j).2 (b j hj k hk),
      fun hlt k hk => (h0' k).2 (d hlt k hk)⟩
