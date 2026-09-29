-- Prove2me | solution 1 for Freiman.middle_small_digit_centers
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:26:08.767986+00:00
-- url     : https://prove2.me/submissions/1c3b1092-3e85-4159-a968-afb7275863a9

import Definitions.Def_Freiman_middleRoots
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_le_of_first_difference
import Theorems.Thm_Freiman_background_period13_value
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.GetD
open Freiman
set_option autoImplicit false
set_option maxHeartbeats 1000000
private theorem root_left_digits (r : Fin 15) :
    ∀ d ∈ (middleRoot r).left, (d : ℕ) ≤ 3 := by
  fin_cases r <;> norm_num [middleRoot, middleRootList]

private theorem root_right_tail_digits (r : Fin 15) (n : ℕ)
    (hn : 0 < n) (hl : n < (middleRoot r).right.length) :
    ((middleRoot r).right.getD n 1 : ℕ) ≤ 3 := by
  fin_cases r <;> norm_num [middleRoot, middleRootList] at hl ⊢
  all_goals first | omega | (interval_cases n <;> norm_num)

private theorem away_four (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (i : ℤ)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (a i : ℕ) ≤ 3 := by
  by_cases hs : 0 ≤ i
  · have hip : 1 < i := by omega
    let n := i.toNat - 1
    have hi : (n:ℤ) + 1 = i := by dsimp [n]; omega
    by_cases hl : (middleRoot r).right.length ≤ n
    · simpa only [hi] using ha.2.2.2.2 n hl
    · have hn : 0 < n := by dsimp [n]; omega
      have hd := ha.2.2.1 n (by omega)
      rw [hi] at hd
      rw [hd]
      exact root_right_tail_digits r n hn (by omega)
  · let n := (-i).toNat - 1
    have hi : -(n:ℤ) - 1 = i := by dsimp [n]; omega
    by_cases hl : (middleRoot r).left.length ≤ n
    · simpa only [hi] using ha.2.2.2.1 n hl
    · have hd := ha.2.1 n (by omega)
      rw [hi] at hd
      rw [hd, List.getD_eq_getElem _ _ (by omega)]
      exact root_left_digits r _ (List.getElem_mem _)

private theorem secondary_index (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (h : ¬ (a 1 : ℕ) ≤ 3) :
    r.val ∈ [5,6,7,8,9,10,11,13] ∧ a 1 = 4 := by
  have hl : 0 < (middleRoot r).right.length := by
    fin_cases r <;> norm_num [middleRoot, middleRootList]
  have hd := ha.2.2.1 0 hl
  norm_num only [Nat.cast_zero, zero_add] at hd
  fin_cases r <;> norm_num [middleRoot, middleRootList] at hd ⊢
  all_goals simp_all
private lemma root_four_positions (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (j : ℤ) (hj : a j = 4) :
    j = 0 ∨ j = 1 := by
  by_cases h0 : j = 0
  · exact Or.inl h0
  by_cases h1 : j = 1
  · exact Or.inr h1
  have hh := away_four r a ha j h0 h1
  rw [hj] at hh
  norm_num at hh

private lemma root_four_right (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (j : ℤ) (hj : a j = 4) :
    a (j + 1) ≠ 1 := by
  rcases root_four_positions r a ha j hj with rfl | rfl
  · have hl : 0 < (middleRoot r).right.length := by
      fin_cases r <;> norm_num [middleRoot, middleRootList]
    have hd := ha.2.2.1 0 hl
    norm_num only [Nat.cast_zero, zero_add] at hd ⊢
    fin_cases r <;> norm_num [middleRoot, middleRootList] at hd <;> simp [hd]
  · have hs := (secondary_index r a ha (by simp [hj])).1
    fin_cases r <;> norm_num at hs
    all_goals
      have hd := ha.2.2.1 1 (by norm_num [middleRoot, middleRootList])
      norm_num [middleRoot, middleRootList] at hd ⊢
      simp [hd]

private lemma root_four_left (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (j : ℤ) (hj : a j = 4)
    (h1 : a (j-1) = 1) : a (j-2) ≠ 3 := by
  rcases root_four_positions r a ha j hj with rfl | rfl
  · have hl : 0 < (middleRoot r).left.length := by
      fin_cases r <;> norm_num [middleRoot, middleRootList]
    have hd := ha.2.1 0 hl
    norm_num only [Nat.cast_zero, neg_zero, zero_sub] at hd h1 ⊢
    fin_cases r <;> norm_num [middleRoot, middleRootList] at hd <;> try simp_all
    all_goals
      have he := ha.2.1 1 (by norm_num [middleRoot, middleRootList])
      norm_num [middleRoot, middleRootList] at he
      simp [he]
  · norm_num only [sub_self] at h1
    have := ha.1
    simp_all

private lemma root_digits_four (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (i : ℤ) : (a i : ℕ) ≤ 4 := by
  by_cases h0 : i=0
  · subst i
    simp [ha.1]
  by_cases h1 : i=1
  · subst i
    have hl : 0 < (middleRoot r).right.length := by
      fin_cases r <;> norm_num [middleRoot, middleRootList]
    have hd := ha.2.2.1 0 hl
    norm_num only [Nat.cast_zero, zero_add] at hd
    fin_cases r <;> norm_num [middleRoot, middleRootList] at hd <;> simp [hd]
  exact (away_four r a ha i h0 h1).trans (by norm_num)

private lemma period13_digit (n : ℕ) :
    (backgroundPeriod13 n : ℕ) = if Even n then 1 else 3 := by
  by_cases he : Even n
  · have hm := Nat.even_iff.mp he
    simp [backgroundPeriod13, gapEventuallyPeriodic, hm, he]
  · have hm : n%2 = 1 := by
      have := Nat.mod_lt n (by omega : 0<2)
      have hh : n%2 ≠ 0 := by simpa only [Nat.even_iff] using he
      omega
    simp [backgroundPeriod13, gapEventuallyPeriodic, hm, he]

private lemma restricted_tail (b : ℕ→ℕ+)
    (hb : ∀ n, (b n : ℕ) ≤ 4)
    (hfront : b 0 = 1 → b 1 ≠ 4)
    (htrip : ∀ n, b n = 3 → b (n+1) = 1 → b (n+2) ≠ 4) :
    cfValue b ≤ (Real.sqrt 21-3)/2 := by
  rw [← background_period13_value]
  apply cfValue_le_of_first_difference
  intro n hp hne
  by_cases he : Even n
  · rw [if_pos he]
    have hd := period13_digit n
    rw [if_pos he] at hd
    have hn := (b n).pos
    have hdne : (b n : ℕ) ≠ (backgroundPeriod13 n : ℕ) := by exact_mod_cast hne
    exact_mod_cast (show (backgroundPeriod13 n : ℕ) < (b n : ℕ) by omega)
  · rw [if_neg he]
    have hd := period13_digit n
    rw [if_neg he] at hd
    have hnmod : n % 2 = 1 := by
      have hh : n%2 ≠ 0 := by simpa only [Nat.even_iff] using he
      omega
    have hn4 : b n ≠ 4 := by
      by_cases hn1 : n=1
      · subst n
        have h0 := hp 0 (by omega)
        have h0' : b 0 = 1 := by
          apply PNat.coe_injective
          change (b 0 : ℕ) = 1
          simpa only [period13_digit, if_pos (by decide : Even 0)] using congrArg (fun x : ℕ+ => (x:ℕ)) h0
        exact hfront h0'
      · have h3 : 3 ≤ n := by omega
        have hpre1 := hp (n-1) (by omega)
        have hpre2 := hp (n-2) (by omega)
        have he1 : Even (n-1) := by rw [Nat.even_iff]; omega
        have he2 : ¬ Even (n-2) := by rw [Nat.even_iff]; omega
        have hb1 : b (n-1) = 1 := by
          apply PNat.coe_injective
          change (b (n-1) : ℕ) = 1
          simpa only [period13_digit, if_pos he1] using congrArg (fun x : ℕ+ => (x:ℕ)) hpre1
        have hb2 : b (n-2) = 3 := by
          apply PNat.coe_injective
          change (b (n-2) : ℕ) = 3
          simpa only [period13_digit, if_neg he2] using congrArg (fun x : ℕ+ => (x:ℕ)) hpre2
        have hh := htrip (n-2) hb2 (by simpa only [show n-2+1=n-1 by omega] using hb1)
        simpa only [show n-2+2=n by omega] using hh
    have hval := hb n
    have hneq : (b n : ℕ) ≠ 4 := by exact_mod_cast hn4
    have hdne : (b n : ℕ) ≠ (backgroundPeriod13 n : ℕ) := by exact_mod_cast hne
    exact_mod_cast (show (b n : ℕ) < (backgroundPeriod13 n : ℕ) by omega)

theorem solution :
    ∀ (r : Fin 15) (a : ℤ→ℕ+) (i : ℤ), middleCompatible (middleRoot r) a → (a i:ℕ) ≤ 3 → localValue a i ≤ Real.sqrt 21 := by
  intro r a i ha hi
  by_cases h2 : (a i:ℕ) ≤ 2
  · have hl := (cf_convergence (fun n : ℕ => a (i-(n:ℤ)-1))).2.2.2.1
    have hr := (cf_convergence (fun n : ℕ => a (i+(n:ℤ)+1))).2.2.2.1
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
    have hp := Real.sqrt_nonneg (21:ℝ)
    have h2' : ((a i:ℕ):ℝ) ≤ 2 := by exact_mod_cast h2
    unfold localValue
    nlinarith only [hl,hr,hs,hp,h2']
  have hai : a i = 3 := by apply PNat.coe_injective; norm_num; omega
  have hl : cfValue (fun n : ℕ => a (i-(n:ℤ)-1)) ≤ (Real.sqrt 21-3)/2 := by
    apply restricted_tail
    · intro n
      exact root_digits_four r a ha _
    · intro h1 h4
      have hbad := root_four_right r a ha (i-2)
        (by convert h4 using 1 <;> congr 1 <;> omega)
      exact hbad (by convert h1 using 1 <;> congr 1 <;> omega)
    · intro n h3 h1 h4
      have hbad := root_four_right r a ha (i-((n+2:ℕ):ℤ)-1) h4
      exact hbad (by convert h1 using 1 <;> congr 1 <;> omega)
  have hr : cfValue (fun n : ℕ => a (i+(n:ℤ)+1)) ≤ (Real.sqrt 21-3)/2 := by
    apply restricted_tail
    · intro n
      exact root_digits_four r a ha _
    · intro h1 h4
      have hbad := root_four_left r a ha (i+2)
        (by convert h4 using 1 <;> congr 1 <;> omega)
        (by convert h1 using 1 <;> congr 1 <;> omega)
      exact hbad (by simpa using hai)
    · intro n h3 h1 h4
      have hbad := root_four_left r a ha (i+((n+2:ℕ):ℤ)+1) h4
        (by convert h1 using 1 <;> congr 1 <;> omega)
      exact hbad (by convert h3 using 1 <;> congr 1 <;> omega)
  unfold localValue
  rw [hai]
  norm_num
  linarith only [hl,hr]
#print axioms solution
