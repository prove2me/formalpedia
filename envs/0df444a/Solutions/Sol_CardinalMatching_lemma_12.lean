-- Prove2me | solution 1 for CardinalMatching.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:55:00.149642+00:00
-- url     : https://prove2.me/submissions/6d84a0a9-99e2-45d0-8060-8ddf939b0230

import Mathlib
import Definitions.Def_CardinalMatching_ModParams

namespace Aux_CardinalMatching_lemma_12
open CardinalMatching

lemma len_flatMap_le {α β : Type} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul (l.map fun a => (f a).length) c (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact h a ha)
  rw [List.length_map, smul_eq_mul] at this
  exact this

lemma chain_len {n : ℕ} (σ : Equiv.Perm (Fin n)) (ε : ℝ) (hε : 0 < ε) (a b : Fin n → ℝ)
    (hab : ∀ t, |b t - a t| ≤ 1) :
    (interpChain σ ε a b).length ≤ n * ⌈1 / ε⌉₊ := by
  unfold interpChain
  rw [List.length_dropLast]
  refine (Nat.sub_le _ _).trans ((len_flatMap_le _ _ ⌈1 / ε⌉₊ ?_).trans (le_of_eq ?_))
  · intro m _
    simp only [List.length_map, List.length_range]
    unfold stepCount
    exact Nat.ceil_mono (div_le_div_of_nonneg_right (hab (σ m)) hε.le)
  · rw [List.length_finRange]

lemma filter_len {n : ℕ} (i : Fin n) :
    ((List.finRange n).filter (fun i' => i < i')).length = n - 1 - (i : ℕ) := by
  have hnd : ((List.finRange n).filter (fun i' => i < i')).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  have hset : ((List.finRange n).filter (fun i' => i < i')).toFinset = Finset.Ioi i := by
    ext j
    simp [List.mem_filter]
  rw [hset, Fin.card_Ioi]

lemma pair_sum (n : ℕ) :
    (∑ i : Fin n, ((List.finRange n).filter (fun i' => i < i')).length) * 2 ≤ n * n := by
  have h1 : ∑ i : Fin n, ((List.finRange n).filter (fun i' => i < i')).length =
      ∑ i ∈ Finset.range n, i := by
    calc ∑ i : Fin n, ((List.finRange n).filter (fun i' => i < i')).length
        = ∑ i : Fin n, (n - 1 - (i : ℕ)) := Finset.sum_congr rfl fun i _ => filter_len i
      _ = ∑ i ∈ Finset.range n, (n - 1 - i) := Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n
      _ = ∑ i ∈ Finset.range n, i := Finset.sum_range_reflect (fun j => j) n
  rw [h1, Finset.sum_range_id_mul_two]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end Aux_CardinalMatching_lemma_12

open Aux_CardinalMatching_lemma_12 in
open CardinalMatching in
theorem solution {n : ℕ} (P : ModParams n) (hP : P.Admissible) :
    Fintype.card P.Agent = Fintype.card P.Good ∧ Fintype.card P.Good ≤ 2 * P.k * n := by
  obtain ⟨hn, hu, hk, hdvd, hε, h4, h4', hd⟩ := hP
  set C : ℕ := ⌈1 / P.ε⌉₊ with hC
  set S : ℕ := ∑ i : Fin n, ((List.finRange n).filter (fun i' => i < i')).length with hS
  have hS2 : S * 2 ≤ n * n := pair_sum n
  have hL : P.interp.length ≤ S * (n * C) := by
    unfold ModParams.interp interpVectors
    rw [List.length_flatMap, ← Fin.sum_univ_def]
    calc _ ≤ ∑ i : Fin n, ((List.finRange n).filter (fun i' => i < i')).length * (n * C) := by
          refine Finset.sum_le_sum fun i _ => len_flatMap_le _ _ _ ?_
          intro i' _
          try dsimp only
          split
          · exact chain_len _ _ hε _ _ fun t => abs_sub_le_iff.mpr
              ⟨by linarith [(hu i t).1, (hu i t).2, (hu i' t).1, (hu i' t).2],
               by linarith [(hu i t).1, (hu i t).2, (hu i' t).1, (hu i' t).2]⟩
          · exact chain_len _ _ hε _ _ fun t => abs_sub_le_iff.mpr
              ⟨by linarith [(hu i t).1, (hu i t).2, (hu i' t).1, (hu i' t).2],
               by linarith [(hu i t).1, (hu i t).2, (hu i' t).1, (hu i' t).2]⟩
      _ = S * (n * C) := by rw [hS, Finset.sum_mul]
  have hr : (n : ℝ) ^ 4 * (C : ℝ) ≤ 2 * (P.k : ℝ) := by
    have h1 : (C : ℝ) ≤ 1 / P.ε + 1 := (Nat.ceil_lt_add_one (one_div_nonneg.mpr hε.le)).le
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    calc (n : ℝ) ^ 4 * (C : ℝ) ≤ (n : ℝ) ^ 4 * (1 / P.ε + 1) := mul_le_mul_of_nonneg_left h1 h0
      _ = (n : ℝ) ^ 4 / P.ε + (n : ℝ) ^ 4 := by ring
      _ ≤ 2 * (P.k : ℝ) := by linarith
  have h3 : n ^ 4 * C ≤ 2 * P.k := by exact_mod_cast hr
  have hnL : 2 * (P.interp.length * n) ≤ 2 * P.k := by
    calc 2 * (P.interp.length * n) ≤ 2 * (S * (n * C) * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hL)
      _ = (n * n * C) * (S * 2) := by ring
      _ ≤ (n * n * C) * (n * n) := Nat.mul_le_mul_left _ hS2
      _ = n ^ 4 * C := by ring
      _ ≤ 2 * P.k := h3
  have hLk : P.interp.length ≤ P.k / n :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hdiv := Nat.div_le_self P.k n
  have hkn : P.k * 1 ≤ P.k * n := Nat.mul_le_mul_left P.k hn
  refine ⟨?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    nlinarith [hn, Nat.zero_le P.k, hkn, hdiv]
