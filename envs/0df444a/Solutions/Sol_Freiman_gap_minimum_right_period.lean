-- Prove2me | solution 1 for Freiman.gap_minimum_right_period
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:23:44.790202+00:00
-- url     : https://prove2.me/submissions/3ada8e08-db51-4db8-a53b-02356ec7c8ed

import Definitions.Def_Freiman_gapModel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open Freiman

private lemma forbid_left_suffix (a : ℤ → ℕ+) (w : List ℕ+)
    (hbad : ∀ i, ¬ gapMatch a i ⟨w,0⟩) (N : ℕ) (hw : 0 < w.length)
    (hlen : w.length ≤ N+1)
    (hvals : ∀ j : ℕ, j < w.length → gapLeftTail a (N-j) = w[j]!) : False := by
  apply hbad (-(N:ℤ)-1)
  refine ⟨hw, ?_⟩
  intro j hj
  change j < w.length at hj
  have he := hvals j hj
  have hjN : j ≤ N := by omega
  simpa only [Nat.cast_zero, sub_zero] using
    (show a (-(N:ℤ)-1+(j:ℤ)) = w[j]! from by
      convert he using 1
      unfold gapLeftTail
      congr 1
      rw [Nat.cast_sub hjN]
      omega)
private lemma forbid_right_block (a : ℤ → ℕ+) (w : List ℕ+)
    (hbad : ∀ i, ¬ gapMatch a i ⟨w,0⟩) (N : ℕ) (hw : 0 < w.length)
    (hvals : ∀ j : ℕ, j < w.length → gapRightTail a (N+j) = w[j]!) : False := by
  apply hbad ((N:ℤ)+1)
  refine ⟨hw, ?_⟩
  intro j hj
  change j < w.length at hj
  have he := hvals j hj
  simpa only [Nat.cast_zero, sub_zero] using
    (show a ((N:ℤ)+1+(j:ℤ)) = w[j]! from by
      convert he using 1
      unfold gapRightTail
      congr 1
      push_cast
      omega)

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapRightTail a) gapBRight (4+6*k+r)) : gapLowerDigit (gapRightTail a) gapBRight (4+6*k+r) := by
  cases k with
  | zero =>
    interval_cases r
    · have hi : 4+6*0+0 = 4 := by omega
      rw [hi] at hp ⊢
      have href : gapBRight 4 = 3 := by
        norm_num [gapBRight, gapEventuallyPeriodic]
      have hpar : Even 4 := ⟨2, by omega⟩
      have hdlo : 1 ≤ (gapRightTail a 4 : ℕ) := (gapRightTail a 4).pos
      have hdhi : (gapRightTail a 4 : ℕ) ≤ 4 := hd (((4 : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapRightTail a 4 : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapRightTail a 4 : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapRightTail a 4 = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [2,4] ((ha [2,4] (by decide)).1) 3 (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a 3 = 2 := by
          rw [hp 3 (by omega)]
          norm_num [gapBRight, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a 4 = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*0+1 = 5 := by omega
      rw [hi] at hp ⊢
      have href : gapBRight 5 = 1 := by
        norm_num [gapBRight, gapEventuallyPeriodic]
      have hpar : ¬ Even 5 := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapRightTail a 5 : ℕ) := (gapRightTail a 5).pos
      have hdhi : (gapRightTail a 5 : ℕ) ≤ 4 := hd (((5 : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapRightTail a 5 : ℕ)
      exact hdlo
    · have hi : 4+6*0+2 = 6 := by omega
      rw [hi] at hp ⊢
      have href : gapBRight 6 = 3 := by
        norm_num [gapBRight, gapEventuallyPeriodic]
      have hpar : Even 6 := ⟨3, by omega⟩
      have hdlo : 1 ≤ (gapRightTail a 6 : ℕ) := (gapRightTail a 6).pos
      have hdhi : (gapRightTail a 6 : ℕ) ≤ 4 := hd (((6 : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapRightTail a 6 : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapRightTail a 6 : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapRightTail a 6 = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [1,4] ((ha [1,4] (by decide)).1) 5 (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a 5 = 1 := by
          rw [hp 5 (by omega)]
          norm_num [gapBRight, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a 6 = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*0+3 = 7 := by omega
      rw [hi] at hp ⊢
      have href : gapBRight 7 = 1 := by
        norm_num [gapBRight, gapEventuallyPeriodic]
      have hpar : ¬ Even 7 := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapRightTail a 7 : ℕ) := (gapRightTail a 7).pos
      have hdhi : (gapRightTail a 7 : ℕ) ≤ 4 := hd (((7 : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapRightTail a 7 : ℕ)
      exact hdlo
    · have hi : 4+6*0+4 = 8 := by omega
      rw [hi] at hp ⊢
      have href : gapBRight 8 = 2 := by
        norm_num [gapBRight, gapEventuallyPeriodic]
      have hpar : Even 8 := ⟨4, by omega⟩
      have hdlo : 1 ≤ (gapRightTail a 8 : ℕ) := (gapRightTail a 8).pos
      have hdhi : (gapRightTail a 8 : ℕ) ≤ 4 := hd (((8 : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapRightTail a 8 : ℕ) ≤ 2
      by_contra hfail
      have hcases : (gapRightTail a 8 : ℕ) = 3 ∨ (gapRightTail a 8 : ℕ) = 4 := by omega
      rcases hcases with hcurNat | hcurNat
      · have hcur : gapRightTail a 8 = 3 := by apply Subtype.ext; exact hcurNat
        apply forbid_right_block a [2,3,1,3,1,3] ((ha [2,3,1,3,1,3] (by decide)).1) 3 (by decide)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapRightTail a 3 = 2 := by
            rw [hp 3 (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a 4 = 3 := by
            rw [hp 4 (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a 5 = 1 := by
            rw [hp 5 (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a 6 = 3 := by
            rw [hp 6 (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a 7 = 1 := by
            rw [hp 7 (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a 8 = 3 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
      · have hcur : gapRightTail a 8 = 4 := by apply Subtype.ext; exact hcurNat
        apply forbid_right_block a [1,4] ((ha [1,4] (by decide)).1) 7 (by decide)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapRightTail a 7 = 1 := by
            rw [hp 7 (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a 8 = 4 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*0+5 = 9 := by omega
      rw [hi] at hp ⊢
      have href : gapBRight 9 = 1 := by
        norm_num [gapBRight, gapEventuallyPeriodic]
      have hpar : ¬ Even 9 := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapRightTail a 9 : ℕ) := (gapRightTail a 9).pos
      have hdhi : (gapRightTail a 9 : ℕ) ≤ 4 := hd (((9 : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapRightTail a 9 : ℕ)
      exact hdlo
  | succ k =>
    interval_cases r
    · have hi : 4+6*(k+1)+0 = 10+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBRight (10+6*k) = 3 := by
        norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (10+6*k < 4) by omega,
          show (10+6*k-4)%6 = 0 by omega]
      have hpar : Even (10+6*k) := ⟨5+3*k, by omega⟩
      have hdlo : 1 ≤ (gapRightTail a (10+6*k) : ℕ) := (gapRightTail a (10+6*k)).pos
      have hdhi : (gapRightTail a (10+6*k) : ℕ) ≤ 4 := hd ((((10+6*k) : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapRightTail a (10+6*k) : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapRightTail a (10+6*k) : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapRightTail a (10+6*k) = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [1,4] ((ha [1,4] (by decide)).1) (9+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (9+6*k) = 1 := by
          rw [hp (9+6*k) (by omega)]
          norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (9+6*k < 4) by omega,
          show (9+6*k-4)%6 = 5 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (10+6*k) = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*(k+1)+1 = 11+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBRight (11+6*k) = 1 := by
        norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (11+6*k < 4) by omega,
          show (11+6*k-4)%6 = 1 by omega]
      have hpar : ¬ Even (11+6*k) := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapRightTail a (11+6*k) : ℕ) := (gapRightTail a (11+6*k)).pos
      have hdhi : (gapRightTail a (11+6*k) : ℕ) ≤ 4 := hd ((((11+6*k) : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapRightTail a (11+6*k) : ℕ)
      exact hdlo
    · have hi : 4+6*(k+1)+2 = 12+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBRight (12+6*k) = 3 := by
        norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (12+6*k < 4) by omega,
          show (12+6*k-4)%6 = 2 by omega]
      have hpar : Even (12+6*k) := ⟨6+3*k, by omega⟩
      have hdlo : 1 ≤ (gapRightTail a (12+6*k) : ℕ) := (gapRightTail a (12+6*k)).pos
      have hdhi : (gapRightTail a (12+6*k) : ℕ) ≤ 4 := hd ((((12+6*k) : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapRightTail a (12+6*k) : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapRightTail a (12+6*k) : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapRightTail a (12+6*k) = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [1,4] ((ha [1,4] (by decide)).1) (11+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (11+6*k) = 1 := by
          rw [hp (11+6*k) (by omega)]
          norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (11+6*k < 4) by omega,
          show (11+6*k-4)%6 = 1 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (12+6*k) = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*(k+1)+3 = 13+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBRight (13+6*k) = 1 := by
        norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (13+6*k < 4) by omega,
          show (13+6*k-4)%6 = 3 by omega]
      have hpar : ¬ Even (13+6*k) := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapRightTail a (13+6*k) : ℕ) := (gapRightTail a (13+6*k)).pos
      have hdhi : (gapRightTail a (13+6*k) : ℕ) ≤ 4 := hd ((((13+6*k) : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapRightTail a (13+6*k) : ℕ)
      exact hdlo
    · have hi : 4+6*(k+1)+4 = 14+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBRight (14+6*k) = 2 := by
        norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (14+6*k < 4) by omega,
          show (14+6*k-4)%6 = 4 by omega]
      have hpar : Even (14+6*k) := ⟨7+3*k, by omega⟩
      have hdlo : 1 ≤ (gapRightTail a (14+6*k) : ℕ) := (gapRightTail a (14+6*k)).pos
      have hdhi : (gapRightTail a (14+6*k) : ℕ) ≤ 4 := hd ((((14+6*k) : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapRightTail a (14+6*k) : ℕ) ≤ 2
      by_contra hfail
      have hcases : (gapRightTail a (14+6*k) : ℕ) = 3 ∨ (gapRightTail a (14+6*k) : ℕ) = 4 := by omega
      rcases hcases with hcurNat | hcurNat
      · have hcur : gapRightTail a (14+6*k) = 3 := by apply Subtype.ext; exact hcurNat
        apply forbid_right_block a [1,3,1,3,1,3] ((ha [1,3,1,3,1,3] (by decide)).1) (9+6*k) (by decide)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapRightTail a (9+6*k) = 1 := by
            rw [hp (9+6*k) (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (9+6*k < 4) by omega,
          show (9+6*k-4)%6 = 5 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a (10+6*k) = 3 := by
            rw [hp (10+6*k) (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (10+6*k < 4) by omega,
          show (10+6*k-4)%6 = 0 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a (11+6*k) = 1 := by
            rw [hp (11+6*k) (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (11+6*k < 4) by omega,
          show (11+6*k-4)%6 = 1 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a (12+6*k) = 3 := by
            rw [hp (12+6*k) (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (12+6*k < 4) by omega,
          show (12+6*k-4)%6 = 2 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a (13+6*k) = 1 := by
            rw [hp (13+6*k) (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (13+6*k < 4) by omega,
          show (13+6*k-4)%6 = 3 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a (14+6*k) = 3 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
      · have hcur : gapRightTail a (14+6*k) = 4 := by apply Subtype.ext; exact hcurNat
        apply forbid_right_block a [1,4] ((ha [1,4] (by decide)).1) (13+6*k) (by decide)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapRightTail a (13+6*k) = 1 := by
            rw [hp (13+6*k) (by omega)]
            norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (13+6*k < 4) by omega,
          show (13+6*k-4)%6 = 3 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapRightTail a (14+6*k) = 4 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*(k+1)+5 = 15+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBRight (15+6*k) = 1 := by
        norm_num [gapBRight, gapEventuallyPeriodic,
          show ¬ (15+6*k < 4) by omega,
          show (15+6*k-4)%6 = 5 by omega]
      have hpar : ¬ Even (15+6*k) := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapRightTail a (15+6*k) : ℕ) := (gapRightTail a (15+6*k)).pos
      have hdhi : (gapRightTail a (15+6*k) : ℕ) ≤ 4 := hd ((((15+6*k) : ℕ):ℤ)+1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapRightTail a (15+6*k) : ℕ)
      exact hdlo

