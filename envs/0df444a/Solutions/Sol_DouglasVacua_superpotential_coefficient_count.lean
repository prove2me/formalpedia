-- Prove2me | solution 1 for DouglasVacua.superpotential_coefficient_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:38:55.804289+00:00
-- url     : https://prove2.me/submissions/94576964-e35f-4ace-9ba6-26596a3a37f1

import Mathlib

open Nat

lemma dvSup_card_eq (n d : ℕ) :
    Set.ncard {e : Fin (n + 1) → ℕ | ∑ i, e i = d} = (d + n).choose d := by
  rw [← Nat.card_coe_set_eq, Set.coe_ofPred,
    ← Nat.card_congr (Sym.equivNatSumOfFintype (Fin (n + 1)) d), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin]
  congr 1
  omega

def dvSup_equiv (n d : ℕ) :
    {e : Fin n → ℕ // ∑ i, e i ≤ d} ≃ {e : Fin (n + 1) → ℕ // ∑ i, e i = d} where
  toFun e := ⟨Fin.cons (d - ∑ i, e.1 i) e.1, by
    have := e.2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun f := ⟨Fin.tail f.1, by
    have := f.2
    simp only [Fin.sum_univ_succ] at this
    simp only [Fin.tail]
    omega⟩
  left_inv e := by
    ext i
    simp [Fin.tail]
  right_inv f := by
    apply Subtype.ext
    have h := f.2
    simp only [Fin.sum_univ_succ] at h
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Fin.tail]
      omega
    · simp [Fin.tail]

lemma dvSup_choose_cast (n d : ℕ) :
    (((d + n).choose d : ℕ) : ℚ) = (d + n)! / (d ! * n !) := by
  rw [Nat.cast_choose ℚ (Nat.le_add_right d n), Nat.add_sub_cancel_left]

open Nat in
theorem solution (n d : ℕ) :
    (Set.ncard {e : Fin n → ℕ | ∑ i, e i ≤ d} : ℚ) = (d + n)! / (d ! * n !) ∧
    (Set.ncard {e : Fin (n + 1) → ℕ | ∑ i, e i = d} : ℚ) = (d + n)! / (d ! * n !) := by
  refine ⟨?_, ?_⟩
  · rw [← dvSup_choose_cast, ← dvSup_card_eq, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, Set.coe_ofPred, Set.coe_ofPred, Nat.card_congr (dvSup_equiv n d)]
  · rw [dvSup_card_eq, dvSup_choose_cast]
