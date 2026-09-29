-- Prove2me | solution 1 for Freiman.gap_maximum_left_period
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:24:48.297618+00:00
-- url     : https://prove2.me/submissions/5b627940-4603-47da-a7d4-6bfc0b1ade7e

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

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapLeftTail a) gapALeft (14+6*k+r)) : gapUpperDigit (gapLeftTail a) gapALeft (14+6*k+r) := by
  interval_cases r
  · have hi : 14+6*k+0 = 14+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapALeft (14+6*k) = 1 := by
      norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (14+6*k < 9) by omega,
        show (14+6*k-9)%6 = 5 by omega]
    have hpar : Even (14+6*k) := ⟨7+3*k, by omega⟩
    have hdlo : 1 ≤ (gapLeftTail a (14+6*k) : ℕ) := (gapLeftTail a (14+6*k)).pos
    have hdhi : (gapLeftTail a (14+6*k) : ℕ) ≤ 4 := hd (-(((14+6*k) : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 1 ≤ (gapLeftTail a (14+6*k) : ℕ)
    exact hdlo
  · have hi : 14+6*k+1 = 15+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapALeft (15+6*k) = 3 := by
      norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (15+6*k < 9) by omega,
        show (15+6*k-9)%6 = 0 by omega]
    have hpar : ¬ Even (15+6*k) := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapLeftTail a (15+6*k) : ℕ) := (gapLeftTail a (15+6*k)).pos
    have hdhi : (gapLeftTail a (15+6*k) : ℕ) ≤ 4 := hd (-(((15+6*k) : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapLeftTail a (15+6*k) : ℕ) ≤ 3
    by_contra hfail
    have hcases : (gapLeftTail a (15+6*k) : ℕ) = 4 := by omega
    have hcurNat := hcases
    have hcur : gapLeftTail a (15+6*k) = 4 := by apply Subtype.ext; exact hcurNat
    apply forbid_left_suffix a [4,1] ((ha.1 [1,4] (by decide)).2) (15+6*k) (by decide) (by norm_num <;> omega)
    intro j hj
    norm_num only [List.length_cons, List.length_nil] at hj
    interval_cases j
    · have he : gapLeftTail a (15+6*k) = 4 := by
        exact hcur
      convert he using 1 <;> congr 1 <;> omega
    · have he : gapLeftTail a (14+6*k) = 1 := by
        rw [hp (14+6*k) (by omega)]
        norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (14+6*k < 9) by omega,
        show (14+6*k-9)%6 = 5 by omega]
      convert he using 1 <;> congr 1 <;> omega
  · have hi : 14+6*k+2 = 16+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapALeft (16+6*k) = 1 := by
      norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (16+6*k < 9) by omega,
        show (16+6*k-9)%6 = 1 by omega]
    have hpar : Even (16+6*k) := ⟨8+3*k, by omega⟩
    have hdlo : 1 ≤ (gapLeftTail a (16+6*k) : ℕ) := (gapLeftTail a (16+6*k)).pos
    have hdhi : (gapLeftTail a (16+6*k) : ℕ) ≤ 4 := hd (-(((16+6*k) : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 1 ≤ (gapLeftTail a (16+6*k) : ℕ)
    exact hdlo
  · have hi : 14+6*k+3 = 17+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapALeft (17+6*k) = 3 := by
      norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (17+6*k < 9) by omega,
        show (17+6*k-9)%6 = 2 by omega]
    have hpar : ¬ Even (17+6*k) := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapLeftTail a (17+6*k) : ℕ) := (gapLeftTail a (17+6*k)).pos
    have hdhi : (gapLeftTail a (17+6*k) : ℕ) ≤ 4 := hd (-(((17+6*k) : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapLeftTail a (17+6*k) : ℕ) ≤ 3
    by_contra hfail
    have hcases : (gapLeftTail a (17+6*k) : ℕ) = 4 := by omega
    have hcurNat := hcases
    have hcur : gapLeftTail a (17+6*k) = 4 := by apply Subtype.ext; exact hcurNat
    apply forbid_left_suffix a [4,1] ((ha.1 [1,4] (by decide)).2) (17+6*k) (by decide) (by norm_num <;> omega)
    intro j hj
    norm_num only [List.length_cons, List.length_nil] at hj
    interval_cases j
    · have he : gapLeftTail a (17+6*k) = 4 := by
        exact hcur
      convert he using 1 <;> congr 1 <;> omega
    · have he : gapLeftTail a (16+6*k) = 1 := by
        rw [hp (16+6*k) (by omega)]
        norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (16+6*k < 9) by omega,
        show (16+6*k-9)%6 = 1 by omega]
      convert he using 1 <;> congr 1 <;> omega
  · have hi : 14+6*k+4 = 18+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapALeft (18+6*k) = 1 := by
      norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (18+6*k < 9) by omega,
        show (18+6*k-9)%6 = 3 by omega]
    have hpar : Even (18+6*k) := ⟨9+3*k, by omega⟩
    have hdlo : 1 ≤ (gapLeftTail a (18+6*k) : ℕ) := (gapLeftTail a (18+6*k)).pos
    have hdhi : (gapLeftTail a (18+6*k) : ℕ) ≤ 4 := hd (-(((18+6*k) : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 1 ≤ (gapLeftTail a (18+6*k) : ℕ)
    exact hdlo
  · have hi : 14+6*k+5 = 19+6*k := by omega
    rw [hi] at hp ⊢
    have href : gapALeft (19+6*k) = 2 := by
      norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (19+6*k < 9) by omega,
        show (19+6*k-9)%6 = 4 by omega]
    have hpar : ¬ Even (19+6*k) := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapLeftTail a (19+6*k) : ℕ) := (gapLeftTail a (19+6*k)).pos
    have hdhi : (gapLeftTail a (19+6*k) : ℕ) ≤ 4 := hd (-(((19+6*k) : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapLeftTail a (19+6*k) : ℕ) ≤ 2
    by_contra hfail
    have hcases : (gapLeftTail a (19+6*k) : ℕ) = 3 ∨ (gapLeftTail a (19+6*k) : ℕ) = 4 := by omega
    rcases hcases with hcurNat | hcurNat
    · have hcur : gapLeftTail a (19+6*k) = 3 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [3,1,3,1,3,1] ((ha.1 [1,3,1,3,1,3] (by decide)).2) (19+6*k) (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a (19+6*k) = 3 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (18+6*k) = 1 := by
          rw [hp (18+6*k) (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (18+6*k < 9) by omega,
        show (18+6*k-9)%6 = 3 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (17+6*k) = 3 := by
          rw [hp (17+6*k) (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (17+6*k < 9) by omega,
        show (17+6*k-9)%6 = 2 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (16+6*k) = 1 := by
          rw [hp (16+6*k) (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (16+6*k < 9) by omega,
        show (16+6*k-9)%6 = 1 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (15+6*k) = 3 := by
          rw [hp (15+6*k) (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (15+6*k < 9) by omega,
        show (15+6*k-9)%6 = 0 by omega]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (14+6*k) = 1 := by
          rw [hp (14+6*k) (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (14+6*k < 9) by omega,
        show (14+6*k-9)%6 = 5 by omega]
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapLeftTail a (19+6*k) = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [4,1] ((ha.1 [1,4] (by decide)).2) (19+6*k) (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a (19+6*k) = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a (18+6*k) = 1 := by
          rw [hp (18+6*k) (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic,
        show ¬ (18+6*k < 9) by omega,
        show (18+6*k-9)%6 = 3 by omega]
        convert he using 1 <;> congr 1 <;> omega

