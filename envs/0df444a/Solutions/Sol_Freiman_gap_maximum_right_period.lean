-- Prove2me | solution 1 for Freiman.gap_maximum_right_period
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:26:13.791772+00:00
-- url     : https://prove2.me/submissions/a69e9227-ea9b-4fe7-8270-764ab4c49cc0

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

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapRightTail a) gapARight (7+6*k+r)) : gapUpperDigit (gapRightTail a) gapARight (7+6*k+r) := by
  interval_cases r
  · have hi : 7+6*k+0 = 7+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapARight (7+6*k) = 4 := by
      norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
    have hpar : ¬ Even (7+6*k) := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapRightTail a (7+6*k) : ℕ) := (gapRightTail a (7+6*k)).pos
    have hdhi : (gapRightTail a (7+6*k) : ℕ) ≤ 4 := hd ((((7+6*k) : ℕ):ℤ)+1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapRightTail a (7+6*k) : ℕ) ≤ 4
    exact hdhi
  · have hi : 7+6*k+1 = 8+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapARight (8+6*k) = 3 := by
      norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (8+6*k < 5) by omega,
        show (8+6*k-5)%6 = 3 by omega]
    have hpar : Even (8+6*k) := ⟨4+3*k, by omega⟩
    have hdlo : 1 ≤ (gapRightTail a (8+6*k) : ℕ) := (gapRightTail a (8+6*k)).pos
    have hdhi : (gapRightTail a (8+6*k) : ℕ) ≤ 4 := hd ((((8+6*k) : ℕ):ℤ)+1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 3 ≤ (gapRightTail a (8+6*k) : ℕ)
    by_contra hfail
    have hcases : (gapRightTail a (8+6*k) : ℕ) = 1 ∨ (gapRightTail a (8+6*k) : ℕ) = 2 := by omega
    rcases hcases with hcurNat | hcurNat
    · have hcur : gapRightTail a (8+6*k) = 1 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,1] ((ha.1 [1,4] (by decide)).2) (7+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (7+6*k) = 4 := by
          rw [hp (7+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (8+6*k) = 1 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapRightTail a (8+6*k) = 2 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,2] ((ha.1 [2,4] (by decide)).2) (7+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (7+6*k) = 4 := by
          rw [hp (7+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (8+6*k) = 2 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
  · have hi : 7+6*k+2 = 9+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapARight (9+6*k) = 2 := by
      norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (9+6*k < 5) by omega,
        show (9+6*k-5)%6 = 4 by omega]
    have hpar : ¬ Even (9+6*k) := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapRightTail a (9+6*k) : ℕ) := (gapRightTail a (9+6*k)).pos
    have hdhi : (gapRightTail a (9+6*k) : ℕ) ≤ 4 := hd ((((9+6*k) : ℕ):ℤ)+1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapRightTail a (9+6*k) : ℕ) ≤ 2
    by_contra hfail
    have hcases : (gapRightTail a (9+6*k) : ℕ) = 3 ∨ (gapRightTail a (9+6*k) : ℕ) = 4 := by omega
    rcases hcases with hcurNat | hcurNat
    · have hcur : gapRightTail a (9+6*k) = 3 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,3,3] ((ha.2).2) (7+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (7+6*k) = 4 := by
          rw [hp (7+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (8+6*k) = 3 := by
          rw [hp (8+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (8+6*k < 5) by omega,
        show (8+6*k-5)%6 = 3 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (9+6*k) = 3 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapRightTail a (9+6*k) = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,4,4,3,4] ((ha.1 [4,4,4,3,4] (by decide)).1) (5+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (5+6*k) = 4 := by
          rw [hp (5+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (5+6*k < 5) by omega,
        show (5+6*k-5)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (6+6*k) = 4 := by
          rw [hp (6+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (6+6*k < 5) by omega,
        show (6+6*k-5)%6 = 1 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (7+6*k) = 4 := by
          rw [hp (7+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (8+6*k) = 3 := by
          rw [hp (8+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (8+6*k < 5) by omega,
        show (8+6*k-5)%6 = 3 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (9+6*k) = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
  · have hi : 7+6*k+3 = 10+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapARight (10+6*k) = 3 := by
      norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (10+6*k < 5) by omega,
        show (10+6*k-5)%6 = 5 by omega]
    have hpar : Even (10+6*k) := ⟨5+3*k, by omega⟩
    have hdlo : 1 ≤ (gapRightTail a (10+6*k) : ℕ) := (gapRightTail a (10+6*k)).pos
    have hdhi : (gapRightTail a (10+6*k) : ℕ) ≤ 4 := hd ((((10+6*k) : ℕ):ℤ)+1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 3 ≤ (gapRightTail a (10+6*k) : ℕ)
    by_contra hfail
    have hcases : (gapRightTail a (10+6*k) : ℕ) = 1 ∨ (gapRightTail a (10+6*k) : ℕ) = 2 := by omega
    rcases hcases with hcurNat | hcurNat
    · have hcur : gapRightTail a (10+6*k) = 1 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,4,4,3,2,1] ((ha.1 [4,4,4,3,2,1] (by decide)).1) (5+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (5+6*k) = 4 := by
          rw [hp (5+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (5+6*k < 5) by omega,
        show (5+6*k-5)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (6+6*k) = 4 := by
          rw [hp (6+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (6+6*k < 5) by omega,
        show (6+6*k-5)%6 = 1 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (7+6*k) = 4 := by
          rw [hp (7+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (8+6*k) = 3 := by
          rw [hp (8+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (8+6*k < 5) by omega,
        show (8+6*k-5)%6 = 3 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (9+6*k) = 2 := by
          rw [hp (9+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (9+6*k < 5) by omega,
        show (9+6*k-5)%6 = 4 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (10+6*k) = 1 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapRightTail a (10+6*k) = 2 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,4,4,3,2,2] ((ha.1 [4,4,4,3,2,2] (by decide)).1) (5+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (5+6*k) = 4 := by
          rw [hp (5+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (5+6*k < 5) by omega,
        show (5+6*k-5)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (6+6*k) = 4 := by
          rw [hp (6+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (6+6*k < 5) by omega,
        show (6+6*k-5)%6 = 1 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (7+6*k) = 4 := by
          rw [hp (7+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (7+6*k < 5) by omega,
        show (7+6*k-5)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (8+6*k) = 3 := by
          rw [hp (8+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (8+6*k < 5) by omega,
        show (8+6*k-5)%6 = 3 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (9+6*k) = 2 := by
          rw [hp (9+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (9+6*k < 5) by omega,
        show (9+6*k-5)%6 = 4 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (10+6*k) = 2 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
  · have hi : 7+6*k+4 = 11+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapARight (11+6*k) = 4 := by
      norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (11+6*k < 5) by omega,
        show (11+6*k-5)%6 = 0 by omega]
    have hpar : ¬ Even (11+6*k) := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapRightTail a (11+6*k) : ℕ) := (gapRightTail a (11+6*k)).pos
    have hdhi : (gapRightTail a (11+6*k) : ℕ) ≤ 4 := hd ((((11+6*k) : ℕ):ℤ)+1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapRightTail a (11+6*k) : ℕ) ≤ 4
    exact hdhi
  · have hi : 7+6*k+5 = 12+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapARight (12+6*k) = 4 := by
      norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (12+6*k < 5) by omega,
        show (12+6*k-5)%6 = 1 by omega]
    have hpar : Even (12+6*k) := ⟨6+3*k, by omega⟩
    have hdlo : 1 ≤ (gapRightTail a (12+6*k) : ℕ) := (gapRightTail a (12+6*k)).pos
    have hdhi : (gapRightTail a (12+6*k) : ℕ) ≤ 4 := hd ((((12+6*k) : ℕ):ℤ)+1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 4 ≤ (gapRightTail a (12+6*k) : ℕ)
    by_contra hfail
    have hcases : (gapRightTail a (12+6*k) : ℕ) = 1 ∨ (gapRightTail a (12+6*k) : ℕ) = 2 ∨ (gapRightTail a (12+6*k) : ℕ) = 3 := by omega
    rcases hcases with hcurNat | hcurNat | hcurNat
    · have hcur : gapRightTail a (12+6*k) = 1 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,1] ((ha.1 [1,4] (by decide)).2) (11+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (11+6*k) = 4 := by
          rw [hp (11+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (11+6*k < 5) by omega,
        show (11+6*k-5)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (12+6*k) = 1 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapRightTail a (12+6*k) = 2 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [4,2] ((ha.1 [2,4] (by decide)).2) (11+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (11+6*k) = 4 := by
          rw [hp (11+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (11+6*k < 5) by omega,
        show (11+6*k-5)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (12+6*k) = 2 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapRightTail a (12+6*k) = 3 := by apply Subtype.ext; exact hcurNat
      apply forbid_right_block a [2,3,4,3] ((ha.1 [2,3,4,3] (by decide)).1) (9+6*k) (by decide)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapRightTail a (9+6*k) = 2 := by
          rw [hp (9+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (9+6*k < 5) by omega,
        show (9+6*k-5)%6 = 4 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (10+6*k) = 3 := by
          rw [hp (10+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (10+6*k < 5) by omega,
        show (10+6*k-5)%6 = 5 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (11+6*k) = 4 := by
          rw [hp (11+6*k) (by omega)]
          norm_num [gapARight, gapEventuallyPeriodic,
        show ¬ (11+6*k < 5) by omega,
        show (11+6*k-5)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapRightTail a (12+6*k) = 3 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega

