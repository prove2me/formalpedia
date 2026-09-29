-- Prove2me | solution 1 for Freiman.upper_small_inward
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:17:34.820208+00:00
-- url     : https://prove2.me/submissions/e2e9cfea-4c8b-4e22-bdfa-8f84fa3ebfd8

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_cf_convergence

open Freiman

set_option maxHeartbeats 800000

private noncomputable def leftTail (a : ℤ → ℕ+) (i : ℤ) : ℝ :=
  cfValue (fun m : ℕ => a (i - (m : ℤ) - 1))

private theorem leftTail_pos (a : ℤ → ℕ+) (i : ℤ) : 0 < leftTail a i :=
  (cf_convergence _).2.2.1

private theorem leftTail_lt_one (a : ℤ → ℕ+) (i : ℤ) : leftTail a i < 1 :=
  (cf_convergence _).2.2.2.1

private theorem leftTail_step (a : ℤ → ℕ+) (i : ℤ) :
    leftTail a i = 1 / (((a (i-1) : ℕ) : ℝ) + leftTail a (i-1)) := by
  have h := (cf_convergence (fun m : ℕ => a (i-(m:ℤ)-1))).2.2.2.2
  have heq : (fun n : ℕ => a (i-((n+1:ℕ):ℤ)-1)) =
      (fun n : ℕ => a ((i-1)-(n:ℤ)-1)) := by
    funext n
    congr 1
    omega
  simpa only [leftTail, Nat.cast_zero, sub_zero, heq] using h

private theorem fixed_facts : (4/13:ℝ) < upperInwardFixed ∧
    1 / (3 + 1 / (4 + upperInwardFixed)) = upperInwardFixed := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3:ℝ)
  have hlow : (45/26:ℝ) < Real.sqrt 3 := by nlinarith
  have hpos : 0 < upperInwardFixed := by unfold upperInwardFixed; linarith
  constructor
  · unfold upperInwardFixed
    linarith
  · have hfour : (4:ℝ) + upperInwardFixed ≠ 0 := by positivity
    have hden : 3 + 1 / (4 + upperInwardFixed) ≠ 0 := by positivity
    field_simp
    unfold upperInwardFixed
    nlinarith

private theorem inward_positive_bound (a : ℤ → ℕ+)
    (hb : ∀ k : ℕ, (a ((k:ℤ)+1) : ℕ) ≤ 4)
    (hadj : ∀ k : ℕ, (a ((k:ℤ)+1) : ℕ) ≤ 2 → (a ((k:ℤ)+2) : ℕ) ≤ 3)
    (hfirst : (a 1 : ℕ) ≠ 4) (hsecond : (a 2 : ℕ) ≠ 4) :
    ∀ k : ℕ, (a ((k:ℤ)+1) : ℕ) = 4 → leftTail a ((k:ℤ)+1) ≤ upperInwardFixed := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro h4
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m+2 := by
      have hk : 2 ≤ k := by
        by_contra hh
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl
        · exact hfirst (by simpa using h4)
        · exact hsecond (by simpa using h4)
      exact ⟨k-2, by omega⟩
    have hprev_low : 3 ≤ (a ((m:ℤ)+2) : ℕ) := by
      have had : (a ((m:ℤ)+2) : ℕ) ≤ 2 → (a ((m:ℤ)+3) : ℕ) ≤ 3 := by
        simpa [Nat.cast_add, add_assoc] using hadj (m+1)
      have h4' : (a ((m:ℤ)+3) : ℕ) = 4 := by
        simpa [Nat.cast_add, add_assoc] using h4
      by_contra hh
      have hv := had (by omega)
      omega
    have hprev_up : (a ((m:ℤ)+2) : ℕ) ≤ 4 := by
      simpa [Nat.cast_add, add_assoc] using hb (m+1)
    have hs1 : leftTail a (((m+2:ℕ):ℤ)+1) =
        1 / (((a ((m:ℤ)+2) : ℕ) : ℝ) + leftTail a ((m:ℤ)+2)) := by
      simpa [Nat.cast_add, add_sub_assoc] using leftTail_step a (((m+2:ℕ):ℤ)+1)
    rcases (show (a ((m:ℤ)+2):ℕ) = 4 ∨ (a ((m:ℤ)+2):ℕ) = 3 by omega) with hprev | hprev
    · have hprevR : ((a ((m:ℤ)+2):ℕ):ℝ) = 4 := by exact_mod_cast hprev
      rw [hs1, hprevR]
      have hsmall : 1 / (4 + leftTail a ((m:ℤ)+2)) ≤ (1/4:ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [leftTail_pos a ((m:ℤ)+2)])
      exact le_trans hsmall (le_of_lt (by linarith [fixed_facts.1]))
    · have hprevR : ((a ((m:ℤ)+2):ℕ):ℝ) = 3 := by exact_mod_cast hprev
      have hs2 : leftTail a ((m:ℤ)+2) =
          1 / (((a ((m:ℤ)+1) : ℕ) : ℝ) + leftTail a ((m:ℤ)+1)) := by
        simpa only [show (m:ℤ)+2-1 = (m:ℤ)+1 by omega] using leftTail_step a ((m:ℤ)+2)
      rw [hs1, hprevR, hs2]
      by_cases hnext : (a ((m:ℤ)+1):ℕ) ≤ 3
      · have hnR : ((a ((m:ℤ)+1):ℕ):ℝ) ≤ 3 := by exact_mod_cast hnext
        have hpR : (0:ℝ) < ((a ((m:ℤ)+1):ℕ):ℝ) := by exact_mod_cast (a ((m:ℤ)+1)).property
        have hden : 0 < ((a ((m:ℤ)+1):ℕ):ℝ) + leftTail a ((m:ℤ)+1) := by
          linarith [leftTail_pos a ((m:ℤ)+1)]
        have hinner : (1/4:ℝ) ≤ 1 / (((a ((m:ℤ)+1):ℕ):ℝ) + leftTail a ((m:ℤ)+1)) :=
          one_div_le_one_div_of_le hden (by linarith [leftTail_lt_one a ((m:ℤ)+1)])
        have hsmall := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3 + 1/4)
          (by linarith : (3+1/4:ℝ) ≤ 3 + 1 / (((a ((m:ℤ)+1):ℕ):ℝ) + leftTail a ((m:ℤ)+1)))
        norm_num at hsmall
        simpa only [one_div] using hsmall.trans (le_of_lt fixed_facts.1)
      · have hn4 : (a ((m:ℤ)+1):ℕ) = 4 := by have hb' := hb m; omega
        have hnR : ((a ((m:ℤ)+1):ℕ):ℝ) = 4 := by exact_mod_cast hn4
        have hi := ih m (by omega) hn4
        have hfixpos : 0 < upperInwardFixed := by linarith [fixed_facts.1]
        rw [hnR]
        have hinner := one_div_le_one_div_of_le
          (by linarith [leftTail_pos a ((m:ℤ)+1)] : (0:ℝ) < 4 + leftTail a ((m:ℤ)+1))
          (by linarith : 4 + leftTail a ((m:ℤ)+1) ≤ 4 + upperInwardFixed)
        have hsmall := one_div_le_one_div_of_le
          (by positivity : (0:ℝ) < 3 + 1/(4+upperInwardFixed))
          (by linarith : 3 + 1/(4+upperInwardFixed) ≤ 3 + 1/(4+leftTail a ((m:ℤ)+1)))
        rw [fixed_facts.2] at hsmall
        exact hsmall

private theorem pad_right (n : ℕ+) (l r : ℕ → ℕ+) (j k : ℕ) :
    upperPad (upperCentral n l r) j ((k : ℤ)+1) = if k+1 ≤ j then r k else 3 := by
  have habs : ((k : ℤ)+1).natAbs=k+1 := by omega
  have hnat : ((k : ℤ)+1).toNat-1=k := by omega
  simp only [upperPad,habs]
  split_ifs
  · rw [upperCentral,if_neg (by omega),if_pos (by omega),hnat]
  · rfl

private theorem pad_reflection (n : ℕ+) (l r : ℕ → ℕ+) (j : ℕ) (i : ℤ) :
    upperPad (upperCentral n l r) j (-i) = upperPad (upperCentral n r l) j i := by
  by_cases hz : i = 0
  · simp [hz, upperPad, upperCentral]
  by_cases hp : 0 < i
  · simp [upperPad, upperCentral, hz, hp, neg_ne_zero.mpr hz, show ¬i < 0 by omega]
  · have hn : i < 0 := by omega
    simp [upperPad, upperCentral, hz, hp, neg_ne_zero.mpr hz, hn]

private theorem one_admissible (r : ℕ → ℕ+) (hr : upperAdmissible r)
    (hr0 : (r 0 : ℕ) ≤ 3) : upperAdmissible (upperOne r) := by
  constructor
  · intro k
    cases k with
    | zero => norm_num [upperOne]
    | succ k => exact hr.1 k
  · intro k hk
    cases k with
    | zero => exact hr0
    | succ k => exact hr.2 k hk

private theorem small_positive (l r : ℕ → ℕ+) (hr : upperAdmissible r)
    (hr0 : (r 0 : ℕ) ≤ 3) (j k : ℕ)
    (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j ((k:ℤ)+1) : ℕ) = 4) :
    leftTail (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) ((k:ℤ)+1) ≤ upperInwardFixed := by
  let a := upperPad (upperCentral 4 (upperOne l) (upperOne r)) j
  have had := one_admissible r hr hr0
  apply inward_positive_bound a _ _ _ _ k h4
  · intro m
    dsimp [a]
    rw [pad_right]
    split_ifs
    · exact had.1 m
    · norm_num
  · intro m hm
    have hin : m+1 ≤ j := by
      by_contra hh
      dsimp [a] at hm
      rw [pad_right, if_neg hh] at hm
      norm_num at hm
    have hmr : (upperOne r m : ℕ) ≤ 2 := by
      dsimp [a] at hm
      simpa only [pad_right, if_pos hin] using hm
    change (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j (((m+1:ℕ):ℤ)+1) : ℕ) ≤ 3
    rw [pad_right]
    split_ifs
    · exact had.2 m hmr
    · norm_num
  · change (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j 1 : ℕ) ≠ 4
    have hh := pad_right 4 (upperOne l) (upperOne r) j 0
    norm_num at hh
    rw [hh]
    split_ifs <;> norm_num [upperOne]
  · change (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j 2 : ℕ) ≠ 4
    have hh := pad_right 4 (upperOne l) (upperOne r) j 1
    norm_num at hh
    rw [hh]
    split_ifs
    · change (r 0 : ℕ) ≠ 4
      omega
    · norm_num

theorem solution (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3)
    (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0)
    (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) = 4) :
    upperInward (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i ≤ upperInwardFixed := by
  by_cases hip : 0 < i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, i = (k:ℤ)+1 := ⟨i.toNat-1, by omega⟩
    rw [hk] at h4 ⊢
    simpa [upperInward, leftTail, show (0:ℤ) < (k:ℤ)+1 by omega] using small_positive l r hr hr0 j k h4
  · have hin : 0 < -i := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -i = (k:ℤ)+1 := ⟨(-i).toNat-1, by omega⟩
    have h4r : (upperPad (upperCentral 4 (upperOne r) (upperOne l)) j ((k:ℤ)+1) : ℕ) = 4 := by
      rw [← hk, ← pad_reflection, neg_neg]
      exact h4
    have hb := small_positive r l hl hl0 j k h4r
    rw [← hk] at hb
    have heq : (fun m : ℕ => upperPad (upperCentral 4 (upperOne r) (upperOne l)) j (-i-(m:ℤ)-1)) =
        (fun m : ℕ => upperPad (upperCentral 4 (upperOne l) (upperOne r)) j (i+(m:ℤ)+1)) := by
      funext m
      rw [← pad_reflection]
      congr 1
      omega
    simpa only [upperInward, if_neg hip, leftTail, heq] using hb
