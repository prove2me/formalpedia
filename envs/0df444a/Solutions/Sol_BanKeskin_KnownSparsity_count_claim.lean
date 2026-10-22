-- Prove2me | solution 1 for BanKeskin.KnownSparsity.count_claim
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:20:51.997063+00:00
-- url     : https://prove2.me/submissions/fcd05144-861a-4e2b-93b3-6d908103de82

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

set_option autoImplicit false
open BanKeskin.KnownSparsity

lemma mm_bk_aux (t c : ℕ) (hc : c ≤ 1) (ht : 5 ≤ t) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ L : ℕ, 1 ≤ L → P (L ^ 2 + c)) :
    (1 / 4 : ℝ) * Real.sqrt (t : ℝ) ≤ (((Finset.Icc 1 t).filter P).card : ℝ) := by
  set n := Nat.sqrt (t - c) with hn
  have hn2 : 2 ≤ n := by
    rw [hn, Nat.le_sqrt]; omega
  have hlt := Nat.lt_succ_sqrt (t - c)
  rw [← hn] at hlt
  have hsq : n * n ≤ t - c := Nat.sqrt_le (t - c)
  have h1 : t ≤ (n + 1) * (n + 1) := by
    simp only [Nat.succ_eq_add_one] at hlt; omega
  have h2 : (n + 1) * (n + 1) ≤ 16 * (n * n) := by nlinarith
  have hcard : n ≤ ((Finset.Icc 1 t).filter P).card := by
    have : (Finset.Icc 1 n).card ≤ ((Finset.Icc 1 t).filter P).card := by
      refine Finset.card_le_card_of_injOn (fun L => L ^ 2 + c) ?_ ?_
      · intro L hL
        simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hL ⊢
        have hL2 : L ^ 2 ≤ n * n := by rw [pow_two]; exact Nat.mul_le_mul hL.2 hL.2
        have hL1 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hL.1
        refine ⟨⟨by omega, by omega⟩, hP L hL.1⟩
      · intro a ha b hb hab
        simp only at hab
        have : a ^ 2 = b ^ 2 := by omega
        exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this
    simpa using this
  have h3 : (t : ℝ) ≤ (4 * (n : ℝ)) ^ 2 := by
    have : t ≤ (4 * n) ^ 2 := by nlinarith
    exact_mod_cast this
  have h4 : Real.sqrt (t : ℝ) ≤ 4 * (n : ℝ) := Real.sqrt_le_iff.2 ⟨by positivity, h3⟩
  have h5 : (n : ℝ) ≤ (((Finset.Icc 1 t).filter P).card : ℝ) := by exact_mod_cast hcard
  linarith

theorem solution (i : Fin 2) (t : ℕ) (ht : 5 ≤ t) :
    (1 / 4 : ℝ) * Real.sqrt (t : ℝ) ≤ (experimentCount i t : ℝ) := by
  classical
  unfold experimentCount
  fin_cases i
  · simp only [Fin.zero_eta, if_true]
    refine mm_bk_aux t 0 (by omega) ht (fun k => inM1 k) ?_
    intro L hL
    exact ⟨L, hL, by simp⟩
  · have : ((1 : Fin 2) = 0) = False := by decide
    simp only [Fin.mk_one, this, if_false]
    refine mm_bk_aux t 1 le_rfl ht (fun k => inM2 k) ?_
    intro L hL
    exact ⟨L, hL, rfl⟩
