-- Prove2me | solution 1 for Freiman.rational_cf_finite_expansion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:56:44.37768+00:00
-- url     : https://prove2.me/submissions/23075d25-b929-4ad8-b67f-70c4f3316c64

import Definitions.Def_Freiman_perronArithmetic

open Freiman

set_option autoImplicit false

private theorem prepend_continuant_data (a : ℕ+) (w : List ℕ+) :
    wordContinuantData (a :: w) =
      ((wordContinuantPrevQ w, wordContinuantQ w),
       ((a : ℕ) * wordContinuantPrevQ w + wordContinuantPrevP w,
        (a : ℕ) * wordContinuantQ w + wordContinuantP w)) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [wordContinuantData, wordContinuantPrevP, wordContinuantP,
      wordContinuantPrevQ, wordContinuantQ]
  | append_singleton w b ih =>
    have step (v : List ℕ+) : wordContinuantData (v ++ [b]) =
        ((wordContinuantP v, (b : ℕ) * wordContinuantP v + wordContinuantPrevP v),
         (wordContinuantQ v, (b : ℕ) * wordContinuantQ v + wordContinuantPrevQ v)) := by
      simp [wordContinuantData, List.foldl_append, wordContinuantP,
        wordContinuantPrevP, wordContinuantQ, wordContinuantPrevQ]
    rw [← List.cons_append, step]
    simp only [wordContinuantP, wordContinuantPrevP, wordContinuantQ,
      wordContinuantPrevQ, ih, step, Prod.mk.injEq]
    constructor
    · constructor
    · constructor
      · trivial
      · ring

theorem solution (p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q) :
    ∃ w : List ℕ+, w ≠ [] ∧
      2 ≤ ((w.getLastD 1 : ℕ+) : ℕ) ∧
      wordContinuantP w = p ∧ wordContinuantQ w = q := by
  induction q using Nat.strong_induction_on generalizing p with
  | h q ih =>
    by_cases hrem : q % p = 0
    · have hpone : p = 1 := hcop.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero hrem)
      subst p
      let a : ℕ+ := ⟨q, by omega⟩
      refine ⟨[a], by simp, ?_, ?_, ?_⟩
      · change 2 ≤ q
        omega
      · simp [wordContinuantP, wordContinuantData]
      · change q * 1 + 0 = q
        omega
    · have hrpos : 0 < q % p := Nat.pos_of_ne_zero hrem
      have hrlt : q % p < p := Nat.mod_lt q hp
      have hrcop : Nat.Coprime (q % p) p := by
        simpa only [Nat.Coprime, ← Nat.gcd_rec] using hcop
      obtain ⟨w, hw, hlast, hP, hQ⟩ := ih p hpq (q % p) hrpos hrlt hrcop
      let a : ℕ+ := ⟨q / p, Nat.div_pos (Nat.le_of_lt hpq) hp⟩
      refine ⟨a :: w, by simp, ?_, ?_, ?_⟩
      · simpa only [List.getLastD_eq_getLast?, List.getLast?_cons_of_ne_nil hw] using hlast
      · simpa only [wordContinuantP, prepend_continuant_data] using hQ
      · change (wordContinuantData (a :: w)).2.2 = q
        rw [prepend_continuant_data]
        change (q / p) * wordContinuantQ w + wordContinuantP w = q
        rw [hP, hQ]
        simpa only [Nat.mul_comm] using Nat.div_add_mod q p
