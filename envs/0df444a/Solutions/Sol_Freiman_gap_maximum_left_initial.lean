-- Prove2me | solution 1 for Freiman.gap_maximum_left_initial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:27:19.347867+00:00
-- url     : https://prove2.me/submissions/0af71dd0-6ffc-4e05-a19e-6a1533dabe9e

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

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (n : ℕ) (hn : n < 14) (hp : gapSameBefore (gapLeftTail a) gapALeft n) : gapUpperDigit (gapLeftTail a) gapALeft n := by
  interval_cases n
  · have he := hs.2 8 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 0 = gapALeft 0 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 7 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 1 = gapALeft 1 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 6 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 2 = gapALeft 2 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 5 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 3 = gapALeft 3 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 4 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 4 = gapALeft 4 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 3 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 5 = gapALeft 5 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 2 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 6 = gapALeft 6 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 1 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 7 = gapALeft 7 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 0 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapLeftTail a 8 = gapALeft 8 := by
      simpa [gapLeftTail, gapALeft, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have href : gapALeft 9 = 3 := by
      norm_num [gapALeft, gapEventuallyPeriodic]
    have hpar : ¬ Even 9 := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapLeftTail a 9 : ℕ) := (gapLeftTail a 9).pos
    have hdhi : (gapLeftTail a 9 : ℕ) ≤ 4 := hd (-((9 : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapLeftTail a 9 : ℕ) ≤ 3
    by_contra hfail
    have hcases : (gapLeftTail a 9 : ℕ) = 4 := by omega
    have hcurNat := hcases
    have hcur : gapLeftTail a 9 = 4 := by apply Subtype.ext; exact hcurNat
    apply forbid_left_suffix a [4,3,3] ((ha.2).2) 9 (by decide) (by norm_num <;> omega)
    intro j hj
    norm_num only [List.length_cons, List.length_nil] at hj
    interval_cases j
    · have he : gapLeftTail a 9 = 4 := by
        exact hcur
      convert he using 1 <;> congr 1 <;> omega
    · have he : gapLeftTail a 8 = 3 := by
        rw [hp 8 (by omega)]
        norm_num [gapALeft, gapEventuallyPeriodic]
      convert he using 1 <;> congr 1 <;> omega
    · have he : gapLeftTail a 7 = 3 := by
        rw [hp 7 (by omega)]
        norm_num [gapALeft, gapEventuallyPeriodic]
      convert he using 1 <;> congr 1 <;> omega
  · have href : gapALeft 10 = 1 := by
      norm_num [gapALeft, gapEventuallyPeriodic]
    have hpar : Even 10 := ⟨5, by omega⟩
    have hdlo : 1 ≤ (gapLeftTail a 10 : ℕ) := (gapLeftTail a 10).pos
    have hdhi : (gapLeftTail a 10 : ℕ) ≤ 4 := hd (-((10 : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 1 ≤ (gapLeftTail a 10 : ℕ)
    exact hdlo
  · have href : gapALeft 11 = 3 := by
      norm_num [gapALeft, gapEventuallyPeriodic]
    have hpar : ¬ Even 11 := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapLeftTail a 11 : ℕ) := (gapLeftTail a 11).pos
    have hdhi : (gapLeftTail a 11 : ℕ) ≤ 4 := hd (-((11 : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapLeftTail a 11 : ℕ) ≤ 3
    by_contra hfail
    have hcases : (gapLeftTail a 11 : ℕ) = 4 := by omega
    have hcurNat := hcases
    have hcur : gapLeftTail a 11 = 4 := by apply Subtype.ext; exact hcurNat
    apply forbid_left_suffix a [4,1] ((ha.1 [1,4] (by decide)).2) 11 (by decide) (by norm_num <;> omega)
    intro j hj
    norm_num only [List.length_cons, List.length_nil] at hj
    interval_cases j
    · have he : gapLeftTail a 11 = 4 := by
        exact hcur
      convert he using 1 <;> congr 1 <;> omega
    · have he : gapLeftTail a 10 = 1 := by
        rw [hp 10 (by omega)]
        norm_num [gapALeft, gapEventuallyPeriodic]
      convert he using 1 <;> congr 1 <;> omega
  · have href : gapALeft 12 = 1 := by
      norm_num [gapALeft, gapEventuallyPeriodic]
    have hpar : Even 12 := ⟨6, by omega⟩
    have hdlo : 1 ≤ (gapLeftTail a 12 : ℕ) := (gapLeftTail a 12).pos
    have hdhi : (gapLeftTail a 12 : ℕ) ≤ 4 := hd (-((12 : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_pos hpar, href]
    change 1 ≤ (gapLeftTail a 12 : ℕ)
    exact hdlo
  · have href : gapALeft 13 = 2 := by
      norm_num [gapALeft, gapEventuallyPeriodic]
    have hpar : ¬ Even 13 := by rintro ⟨t, ht⟩; omega
    have hdlo : 1 ≤ (gapLeftTail a 13 : ℕ) := (gapLeftTail a 13).pos
    have hdhi : (gapLeftTail a 13 : ℕ) ≤ 4 := hd (-((13 : ℕ):ℤ)-1)
    unfold gapUpperDigit
    rw [if_neg hpar, href]
    change (gapLeftTail a 13 : ℕ) ≤ 2
    by_contra hfail
    have hcases : (gapLeftTail a 13 : ℕ) = 3 ∨ (gapLeftTail a 13 : ℕ) = 4 := by omega
    rcases hcases with hcurNat | hcurNat
    · have hcur : gapLeftTail a 13 = 3 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [3,1,3,1,3,3,3] ((ha.1 [3,1,3,1,3,3,3] (by decide)).1) 13 (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a 13 = 3 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 12 = 1 := by
          rw [hp 12 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 11 = 3 := by
          rw [hp 11 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 10 = 1 := by
          rw [hp 10 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 9 = 3 := by
          rw [hp 9 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 8 = 3 := by
          rw [hp 8 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 7 = 3 := by
          rw [hp 7 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega
    · have hcur : gapLeftTail a 13 = 4 := by apply Subtype.ext; exact hcurNat
      apply forbid_left_suffix a [4,1] ((ha.1 [1,4] (by decide)).2) 13 (by decide) (by norm_num <;> omega)
      intro j hj
      norm_num only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · have he : gapLeftTail a 13 = 4 := by
          exact hcur
        convert he using 1 <;> congr 1 <;> omega
      · have he : gapLeftTail a 12 = 1 := by
          rw [hp 12 (by omega)]
          norm_num [gapALeft, gapEventuallyPeriodic]
        convert he using 1 <;> congr 1 <;> omega

