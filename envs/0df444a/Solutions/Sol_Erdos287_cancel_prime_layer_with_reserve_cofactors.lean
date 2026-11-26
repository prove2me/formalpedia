-- Prove2me | solution 1 for Erdos287.cancel_prime_layer_with_reserve_cofactors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:42:51.305855+00:00
-- url     : https://prove2.me/submissions/024a59ab-c67d-40e4-b102-c06a68912975

import Mathlib

open Finset
open scoped Pointwise

set_option autoImplicit false

private def subsetResidues {p : ℕ} (w : ℕ → ZMod p) (S : Finset ℕ) : Finset (ZMod p) :=
  S.powerset.image (fun U => ∑ n ∈ U, w n)

private theorem subset_residue_count {p : ℕ} (hp : p.Prime) (w : ℕ → ZMod p)
    (S : Finset ℕ) (hnz : ∀ n ∈ S, w n ≠ 0) :
    min p (S.card + 1) ≤ (subsetResidues w S).card := by
  induction S using Finset.induction_on with
  | empty => simp [subsetResidues]
  | insert n S hn ih =>
    let T : Finset (ZMod p) := {0, w n}
    have hT : T.card = 2 := by
      have hn' := hnz n (mem_insert_self n S)
      simp [T, hn'.symm]
    have hS₀ : 0 ∈ subsetResidues w S := by
      exact mem_image.mpr ⟨∅, by simp, by simp⟩
    have hT₀ : 0 ∈ T := by simp [T]
    have hsub : subsetResidues w S + T ⊆ subsetResidues w (insert n S) := by
      intro g hg
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hg
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hx
      have hSU : U ⊆ S := mem_powerset.mp hU
      simp only [T, mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · rw [add_zero]
        exact mem_image.mpr ⟨U, mem_powerset.mpr (hSU.trans (subset_insert n S)), rfl⟩
      · refine mem_image.mpr ⟨insert n U, mem_powerset.mpr (insert_subset_insert _ hSU), ?_⟩
        rw [sum_insert (fun h => hn (hSU h)), add_comm]
    have hcount := ZMod.cauchy_davenport hp ⟨0, hS₀⟩ ⟨0, hT₀⟩
    rw [hT] at hcount
    have hl := ih (fun k hk => hnz k (mem_insert_of_mem hk))
    have hu := hcount.trans (card_le_card hsub)
    rw [card_insert_of_notMem hn]
    omega

/-- A reservoir of cofactors can eliminate one prime-power layer from a
reciprocal sum while adding at most one less than the prime many terms. -/
theorem solution (p e L : ℕ) (A : ℤ) (S : Finset ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hL : ¬ p ∣ L) (hcard : p - 1 ≤ S.card) (hcof : ∀ c ∈ S, 0 < c ∧ c ∣ L) :
    ∃ T ⊆ S, T.card ≤ p - 1 ∧ ∃ K : ℤ,
      (A : ℚ) / ((p : ℚ) ^ e * L) + (∑ c ∈ T, (1 : ℚ) / ((p : ℚ) ^ e * c)) =
        (K : ℚ) / ((p : ℚ) ^ (e - 1) * L) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let w (c : ℕ) := ((L / c : ℕ) : ZMod p)
  obtain ⟨U, hUS, hU⟩ := exists_subset_card_eq hcard
  have hnz (c : ℕ) (hc : c ∈ U) : w c ≠ 0 := by
    intro h
    have hd : p ∣ L / c := (ZMod.natCast_eq_zero_iff (L / c) p).mp h
    apply hL
    rw [← Nat.div_mul_cancel (hcof c (hUS hc)).2]
    exact dvd_mul_of_dvd_left hd c
  have hres := subset_residue_count hp w U hnz
  rw [hU, Nat.sub_add_cancel hp.one_lt.le, min_self] at hres
  have hc := card_le_univ (s := subsetResidues w U)
  rw [ZMod.card] at hc
  have hall : subsetResidues w U = univ := eq_univ_of_card _ (by
    rw [ZMod.card]
    exact le_antisymm hc hres)
  have hb : -(A : ZMod p) ∈ subsetResidues w U := by rw [hall]; exact mem_univ _
  obtain ⟨T, hTU, hsum⟩ := mem_image.mp hb
  have hsub : T ⊆ U := mem_powerset.mp hTU
  have hTS := hsub.trans hUS
  let N : ℤ := A + ∑ c ∈ T, ((L / c : ℕ) : ℤ)
  have hzero : (N : ZMod p) = 0 := by
    simp only [N, Int.cast_add, Int.cast_sum, Int.cast_natCast]
    change (A : ZMod p) + (∑ c ∈ T, w c) = 0
    rw [hsum, add_neg_cancel]
  obtain ⟨K, hNK⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd N p).mp hzero
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hLpos : 0 < L := Nat.pos_of_ne_zero fun hz => hL (by rw [hz]; exact dvd_zero p)
  have hLQ : (0 : ℚ) < L := by exact_mod_cast hLpos
  have hS : (∑ c ∈ T, (1 : ℚ) / ((p : ℚ) ^ e * c)) =
      (∑ c ∈ T, ((L / c : ℕ) : ℚ)) / ((p : ℚ) ^ e * L) := by
    rw [sum_div]
    refine sum_congr rfl fun c hc => ?_
    have hcQ : (0 : ℚ) < c := by exact_mod_cast (hcof c (hTS hc)).1
    have hLcancel : ((L / c : ℕ) : ℚ) * c = L := by
      exact_mod_cast Nat.div_mul_cancel (hcof c (hTS hc)).2
    apply (div_eq_div_iff (mul_pos (pow_pos hpQ _) hcQ).ne' (mul_pos (pow_pos hpQ _) hLQ).ne').mpr
    calc
      _ = (p : ℚ) ^ e * (((L / c : ℕ) : ℚ) * c) := by rw [one_mul, hLcancel]
      _ = _ := by ring
  have hcast : (A : ℚ) + ∑ c ∈ T, ((L / c : ℕ) : ℚ) = (N : ℚ) := by
    simp only [N, Int.cast_add, Int.cast_sum, Int.cast_natCast]
  have heq : (p : ℚ) ^ e = (p : ℚ) ^ (e - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  refine ⟨T, hTS, (card_le_card hsub).trans_eq hU, K, ?_⟩
  rw [hS, ← add_div, hcast, hNK, Int.cast_mul, Int.cast_natCast, heq]
  field_simp

