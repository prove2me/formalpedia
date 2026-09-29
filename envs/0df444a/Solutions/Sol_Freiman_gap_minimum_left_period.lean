-- Prove2me | solution 1 for Freiman.gap_minimum_left_period
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:25:53.814294+00:00
-- url     : https://prove2.me/submissions/ce89e6de-12d5-4251-ab68-fab040b3a093

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

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapLeftTail a) gapBLeft (4+6*k+r)) : gapLowerDigit (gapLeftTail a) gapBLeft (4+6*k+r) := by
  cases k with
  | zero =>
    interval_cases r
    · have hi : 4+6*0+0 = 4 := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft 4 = 3 := by
        norm_num [gapBLeft, gapEventuallyPeriodic]
      have hpar : Even 4 := ⟨2, by omega⟩
      have hdlo : 1 ≤ (gapLeftTail a 4 : ℕ) := (gapLeftTail a 4).pos
      have hdhi : (gapLeftTail a 4 : ℕ) ≤ 4 := hd (-((4 : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapLeftTail a 4 : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapLeftTail a 4 : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapLeftTail a 4 = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [4,1] ((ha [1,4] (by decide)).2) 4 (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a 4 = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 3 = 1 := by
          rw [hp 3 (by omega)]
          norm_num [gapBLeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*0+1 = 5 := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft 5 = 1 := by
        norm_num [gapBLeft, gapEventuallyPeriodic]
      have hpar : ¬ Even 5 := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapLeftTail a 5 : ℕ) := (gapLeftTail a 5).pos
      have hdhi : (gapLeftTail a 5 : ℕ) ≤ 4 := hd (-((5 : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapLeftTail a 5 : ℕ)
      exact hdlo
    · have hi : 4+6*0+2 = 6 := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft 6 = 3 := by
        norm_num [gapBLeft, gapEventuallyPeriodic]
      have hpar : Even 6 := ⟨3, by omega⟩
      have hdlo : 1 ≤ (gapLeftTail a 6 : ℕ) := (gapLeftTail a 6).pos
      have hdhi : (gapLeftTail a 6 : ℕ) ≤ 4 := hd (-((6 : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapLeftTail a 6 : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapLeftTail a 6 : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapLeftTail a 6 = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [4,1] ((ha [1,4] (by decide)).2) 6 (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a 6 = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 5 = 1 := by
          rw [hp 5 (by omega)]
          norm_num [gapBLeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*0+3 = 7 := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft 7 = 1 := by
        norm_num [gapBLeft, gapEventuallyPeriodic]
      have hpar : ¬ Even 7 := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapLeftTail a 7 : ℕ) := (gapLeftTail a 7).pos
      have hdhi : (gapLeftTail a 7 : ℕ) ≤ 4 := hd (-((7 : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapLeftTail a 7 : ℕ)
      exact hdlo
    · have hi : 4+6*0+4 = 8 := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft 8 = 2 := by
        norm_num [gapBLeft, gapEventuallyPeriodic]
      have hpar : Even 8 := ⟨4, by omega⟩
      have hdlo : 1 ≤ (gapLeftTail a 8 : ℕ) := (gapLeftTail a 8).pos
      have hdhi : (gapLeftTail a 8 : ℕ) ≤ 4 := hd (-((8 : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapLeftTail a 8 : ℕ) ≤ 2
      by_contra hfail
      have hcases : (gapLeftTail a 8 : ℕ) = 3 ∨ (gapLeftTail a 8 : ℕ) = 4 := by omega
      rcases hcases with hcurNat | hcurNat
      · have hcur : gapLeftTail a 8 = 3 := by apply Subtype.ext; exact hcurNat
        apply forbid_left_suffix a [3,1,3,1,3,1] ((ha [1,3,1,3,1,3] (by decide)).2) 8 (by decide) (by norm_num <;> omega)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapLeftTail a 8 = 3 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a 7 = 1 := by
            rw [hp 7 (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a 6 = 3 := by
            rw [hp 6 (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a 5 = 1 := by
            rw [hp 5 (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a 4 = 3 := by
            rw [hp 4 (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a 3 = 1 := by
            rw [hp 3 (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
      · have hcur : gapLeftTail a 8 = 4 := by apply Subtype.ext; exact hcurNat
        apply forbid_left_suffix a [4,1] ((ha [1,4] (by decide)).2) 8 (by decide) (by norm_num <;> omega)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapLeftTail a 8 = 4 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a 7 = 1 := by
            rw [hp 7 (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic]
          convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*0+5 = 9 := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft 9 = 1 := by
        norm_num [gapBLeft, gapEventuallyPeriodic]
      have hpar : ¬ Even 9 := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapLeftTail a 9 : ℕ) := (gapLeftTail a 9).pos
      have hdhi : (gapLeftTail a 9 : ℕ) ≤ 4 := hd (-((9 : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapLeftTail a 9 : ℕ)
      exact hdlo
  | succ k =>
    interval_cases r
    · have hi : 4+6*(k+1)+0 = 10+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft (10+6*k) = 3 := by
        norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (10+6*k < 4) by omega,
          show (10+6*k-4)%6 = 0 by omega]
      have hpar : Even (10+6*k) := ⟨5+3*k, by omega⟩
      have hdlo : 1 ≤ (gapLeftTail a (10+6*k) : ℕ) := (gapLeftTail a (10+6*k)).pos
      have hdhi : (gapLeftTail a (10+6*k) : ℕ) ≤ 4 := hd (-(((10+6*k) : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapLeftTail a (10+6*k) : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapLeftTail a (10+6*k) : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapLeftTail a (10+6*k) = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [4,1] ((ha [1,4] (by decide)).2) (10+6*k) (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a (10+6*k) = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (9+6*k) = 1 := by
          rw [hp (9+6*k) (by omega)]
          norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (9+6*k < 4) by omega,
          show (9+6*k-4)%6 = 5 by omega]
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*(k+1)+1 = 11+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft (11+6*k) = 1 := by
        norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (11+6*k < 4) by omega,
          show (11+6*k-4)%6 = 1 by omega]
      have hpar : ¬ Even (11+6*k) := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapLeftTail a (11+6*k) : ℕ) := (gapLeftTail a (11+6*k)).pos
      have hdhi : (gapLeftTail a (11+6*k) : ℕ) ≤ 4 := hd (-(((11+6*k) : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapLeftTail a (11+6*k) : ℕ)
      exact hdlo
    · have hi : 4+6*(k+1)+2 = 12+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft (12+6*k) = 3 := by
        norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (12+6*k < 4) by omega,
          show (12+6*k-4)%6 = 2 by omega]
      have hpar : Even (12+6*k) := ⟨6+3*k, by omega⟩
      have hdlo : 1 ≤ (gapLeftTail a (12+6*k) : ℕ) := (gapLeftTail a (12+6*k)).pos
      have hdhi : (gapLeftTail a (12+6*k) : ℕ) ≤ 4 := hd (-(((12+6*k) : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapLeftTail a (12+6*k) : ℕ) ≤ 3
      by_contra hfail
      have hcases : (gapLeftTail a (12+6*k) : ℕ) = 4 := by omega
      have hcurNat := hcases
      have hcur : gapLeftTail a (12+6*k) = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [4,1] ((ha [1,4] (by decide)).2) (12+6*k) (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a (12+6*k) = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (11+6*k) = 1 := by
          rw [hp (11+6*k) (by omega)]
          norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (11+6*k < 4) by omega,
          show (11+6*k-4)%6 = 1 by omega]
        convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*(k+1)+3 = 13+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft (13+6*k) = 1 := by
        norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (13+6*k < 4) by omega,
          show (13+6*k-4)%6 = 3 by omega]
      have hpar : ¬ Even (13+6*k) := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapLeftTail a (13+6*k) : ℕ) := (gapLeftTail a (13+6*k)).pos
      have hdhi : (gapLeftTail a (13+6*k) : ℕ) ≤ 4 := hd (-(((13+6*k) : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapLeftTail a (13+6*k) : ℕ)
      exact hdlo
    · have hi : 4+6*(k+1)+4 = 14+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft (14+6*k) = 2 := by
        norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (14+6*k < 4) by omega,
          show (14+6*k-4)%6 = 4 by omega]
      have hpar : Even (14+6*k) := ⟨7+3*k, by omega⟩
      have hdlo : 1 ≤ (gapLeftTail a (14+6*k) : ℕ) := (gapLeftTail a (14+6*k)).pos
      have hdhi : (gapLeftTail a (14+6*k) : ℕ) ≤ 4 := hd (-(((14+6*k) : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_pos hpar, href]
      change (gapLeftTail a (14+6*k) : ℕ) ≤ 2
      by_contra hfail
      have hcases : (gapLeftTail a (14+6*k) : ℕ) = 3 ∨ (gapLeftTail a (14+6*k) : ℕ) = 4 := by omega
      rcases hcases with hcurNat | hcurNat
      · have hcur : gapLeftTail a (14+6*k) = 3 := by apply Subtype.ext; exact hcurNat
        apply forbid_left_suffix a [3,1,3,1,3,1] ((ha [1,3,1,3,1,3] (by decide)).2) (14+6*k) (by decide) (by norm_num <;> omega)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapLeftTail a (14+6*k) = 3 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a (13+6*k) = 1 := by
            rw [hp (13+6*k) (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (13+6*k < 4) by omega,
          show (13+6*k-4)%6 = 3 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a (12+6*k) = 3 := by
            rw [hp (12+6*k) (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (12+6*k < 4) by omega,
          show (12+6*k-4)%6 = 2 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a (11+6*k) = 1 := by
            rw [hp (11+6*k) (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (11+6*k < 4) by omega,
          show (11+6*k-4)%6 = 1 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a (10+6*k) = 3 := by
            rw [hp (10+6*k) (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (10+6*k < 4) by omega,
          show (10+6*k-4)%6 = 0 by omega]
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a (9+6*k) = 1 := by
            rw [hp (9+6*k) (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (9+6*k < 4) by omega,
          show (9+6*k-4)%6 = 5 by omega]
          convert he using 1 <;> congr 1 <;> omega
      · have hcur : gapLeftTail a (14+6*k) = 4 := by apply Subtype.ext; exact hcurNat
        apply forbid_left_suffix a [4,1] ((ha [1,4] (by decide)).2) (14+6*k) (by decide) (by norm_num <;> omega)
        intro j hj
        norm_num only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · have he : gapLeftTail a (14+6*k) = 4 := by
            exact hcur
          convert he using 1 <;> congr 1 <;> omega
        · have he : gapLeftTail a (13+6*k) = 1 := by
            rw [hp (13+6*k) (by omega)]
            norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (13+6*k < 4) by omega,
          show (13+6*k-4)%6 = 3 by omega]
          convert he using 1 <;> congr 1 <;> omega
    · have hi : 4+6*(k+1)+5 = 15+6*k := by omega
      rw [hi] at hp ⊢
      have href : gapBLeft (15+6*k) = 1 := by
        norm_num [gapBLeft, gapEventuallyPeriodic,
          show ¬ (15+6*k < 4) by omega,
          show (15+6*k-4)%6 = 5 by omega]
      have hpar : ¬ Even (15+6*k) := by rintro ⟨t, ht⟩; omega
      have hdlo : 1 ≤ (gapLeftTail a (15+6*k) : ℕ) := (gapLeftTail a (15+6*k)).pos
      have hdhi : (gapLeftTail a (15+6*k) : ℕ) ≤ 4 := hd (-(((15+6*k) : ℕ):ℤ)-1)
      unfold gapLowerDigit
      rw [if_neg hpar, href]
      change 1 ≤ (gapLeftTail a (15+6*k) : ℕ)
      exact hdlo

