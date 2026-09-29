-- Prove2me | solution 1 for Freiman.lowerJ_reverse_cross
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T15:50:14.891981+00:00
-- url     : https://prove2.me/submissions/bfa75b9a-37e0-4dcf-a08e-37e8463b1031

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Freiman

namespace M7JO

lemma pe_nonneg (w : List ℕ+) : ∀ (x : ℝ), 0 ≤ x → 0 ≤ prefixEval w x := by
  induction w with
  | nil => intro x hx; simpa [prefixEval] using hx
  | cons a w ih =>
      intro x hx
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have h := ih x hx
      have hd : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      simp only [prefixEval]
      positivity

lemma pe_append (u : List ℕ+) : ∀ (v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => intro v x; simp [prefixEval]
  | cons a u ih => intro v x; simp only [List.cons_append, prefixEval, ih]

lemma pe_sign (w : List ℕ+) : ∀ (x y : ℝ), 0 ≤ x → x < y →
    0 < (-1:ℝ)^w.length * (prefixEval w y - prefixEval w x) := by
  induction w with
  | nil => intro x y hx hxy; simp [prefixEval]; linarith
  | cons a w ih =>
      intro x y hx hxy
      have hy : (0:ℝ) ≤ y := le_of_lt (lt_of_le_of_lt hx hxy)
      have h := ih x y hx hxy
      have nx := pe_nonneg w x hx
      have ny := pe_nonneg w y hy
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have dx : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      have dy : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w y := by linarith
      have hD : (0:ℝ) < (((a:ℕ):ℝ) + prefixEval w y) * (((a:ℕ):ℝ) + prefixEval w x) :=
        mul_pos dy dx
      have hpos := div_pos h hD
      have heq : ((-1:ℝ)^w.length * (prefixEval w y - prefixEval w x))
            / ((((a:ℕ):ℝ) + prefixEval w y) * (((a:ℕ):ℝ) + prefixEval w x))
          = (-1:ℝ)^(a :: w).length * (prefixEval (a :: w) y - prefixEval (a :: w) x) := by
        simp only [prefixEval, List.length_cons, pow_succ]
        field_simp
        ring
      rwa [heq] at hpos

lemma sign_eq (m n : ℕ) (h : m % 2 = n % 2) : ((-1:ℝ))^m = ((-1:ℝ))^n := by
  rcases Nat.even_or_odd m with hm | hm
  · have hn : Even n := by
      rw [Nat.even_iff] at hm ⊢; omega
    rw [hm.neg_one_pow, hn.neg_one_pow]
  · have hn : Odd n := by
      rw [Nat.odd_iff] at hm ⊢; omega
    rw [hm.neg_one_pow, hn.neg_one_pow]

end M7JO

open M7JO

theorem solution (hn : lowerJSignFacts) (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) : lowerJReverseCross p k := by
  classical
  have htau : (0:ℝ) ≤ lowerTau := by
    have h1 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    unfold lowerTau
    nlinarith
  have hA0 : (0:ℝ) ≤ lowerJA := by
    show (0:ℝ) ≤ prefixEval [3] lowerTau
    exact pe_nonneg _ _ htau
  have h7 : (0:ℝ) < lowerJD - lowerJA := hn 7
  have h8 : (0:ℝ) < lowerJC - lowerJD := hn 8
  have h11 : (0:ℝ) < lowerJB - lowerJIter 2 lowerJA := hn 11
  have h12 : (0:ℝ) < lowerJB - lowerJIter 2 lowerJC := hn 12
  have hC0 : (0:ℝ) ≤ lowerJC := by linarith
  have hIA0 : (0:ℝ) ≤ lowerJIter 2 lowerJA := by
    show (0:ℝ) ≤ prefixEval (List.replicate 2 (3:ℕ+)) lowerJA
    exact pe_nonneg _ _ hA0
  have hIC0 : (0:ℝ) ≤ lowerJIter 2 lowerJC := by
    show (0:ℝ) ≤ prefixEval (List.replicate 2 (3:ℕ+)) lowerJC
    exact pe_nonneg _ _ hC0
  have hIAB : lowerJIter 2 lowerJA < lowerJB := by linarith
  have hICB : lowerJIter 2 lowerJC < lowerJB := by linarith
  set q := lowerNormalize p with hq
  have hpar : q.1.length % 2 = q.2.length % 2 := by
    have hm : ¬ lowerMixed p := hr.1
    unfold lowerMixed at hm
    by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hq, lowerNormalize, if_pos hh]; omega
    · simp only [hq, lowerNormalize, if_neg hh]; omega
  set R := List.replicate k (3:ℕ+) with hR
  have hlen1 : (q.1 ++ R).length = q.1.length + k := by simp [hR]
  have hlen2 : (q.2 ++ R).length = q.2.length + k := by simp [hR]
  have key1 : 0 < (-1:ℝ)^(q.1.length + k) *
      (prefixEval (q.1 ++ R) lowerJB - prefixEval (q.1 ++ R) (lowerJIter 2 lowerJA)) := by
    have := pe_sign (q.1 ++ R) (lowerJIter 2 lowerJA) lowerJB hIA0 hIAB
    rwa [hlen1] at this
  have key2 : 0 < (-1:ℝ)^(q.2.length + k) *
      (prefixEval (q.2 ++ R) lowerJB - prefixEval (q.2 ++ R) (lowerJIter 2 lowerJC)) := by
    have := pe_sign (q.2 ++ R) (lowerJIter 2 lowerJC) lowerJB hIC0 hICB
    rwa [hlen2] at this
  rw [sign_eq _ (q.1.length + k) (by omega)] at key2
  have hrep : List.replicate (k+2) (3:ℕ+) = R ++ List.replicate 2 (3:ℕ+) := by
    rw [hR, ← List.replicate_add]
  have hcombine : 0 < (-1:ℝ)^(q.1.length + k) * (lowerJInnerB p k - lowerJInnerA p (k+2)) := by
    have e1 : lowerJInnerB p k - lowerJInnerA p (k+2)
        = (prefixEval (q.1 ++ R) lowerJB - prefixEval (q.1 ++ R) (lowerJIter 2 lowerJA))
          + (prefixEval (q.2 ++ R) lowerJB - prefixEval (q.2 ++ R) (lowerJIter 2 lowerJC)) := by
      simp only [lowerJInnerA, lowerJInnerB, lowerJActual, lowerJIter, hrep, pe_append, hR, ← hq]
      ring
    rw [e1, mul_add]
    linarith
  by_cases hev : lowerJEven p k
  · have hE : Even (q.1.length + k) := by
      have h0 : (q.1.length + k) % 2 = 0 := hev
      rw [Nat.even_iff]; exact h0
    rw [hE.neg_one_pow, one_mul] at hcombine
    simp only [lowerJReverseCross, if_pos hev]
    linarith
  · have hO : Odd (q.1.length + k) := by
      have h0 : ¬ ((q.1.length + k) % 2 = 0) := hev
      rw [Nat.odd_iff]; omega
    rw [hO.neg_one_pow] at hcombine
    simp only [lowerJReverseCross, if_neg hev]
    linarith
