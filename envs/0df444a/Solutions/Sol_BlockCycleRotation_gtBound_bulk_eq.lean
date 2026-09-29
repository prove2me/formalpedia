-- Prove2me | solution 1 for BlockCycleRotation.gtBound_bulk_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:17:43.264562+00:00
-- url     : https://prove2.me/submissions/45999cc6-35af-4580-8d05-9c3da24141ea

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **For a bulk pair the first branch of the cut-off wins.**

`Y = min(m/(a+a'), (m - d a²)/a')`, and the paper observes that the first term
is the smaller exactly when `d·a·(a+a') ≤ m`.  In the floored form used here
that reads `gtBound m d a a' = (m-1)/(a+a') + 1`. -/
theorem solution {m d a a' : ℕ} (hd : 0 < d) (ha' : 1 ≤ a') (haa : a' < a)
    (hbulk : d * a * (a + a') ≤ m) :
    gtBound m d a a' = (m - 1) / (a + a') + 1:= by
  have ha : 0 < a := by omega
  have hs : 0 < a + a' := by omega
  have hda : 1 ≤ d * a := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hm2 : d * a * a + 1 ≤ m := by nlinarith
  have hdm := Nat.div_add_mod (m - 1) (a + a')
  have hr : (m - 1) % (a + a') < a + a' := Nat.mod_lt _ hs
  set q := (m - 1) / (a + a') with hq
  set r := (m - 1) % (a + a') with hrr
  have hmeq : m = (a + a') * q + r + 1 := by omega
  have hexp : (a + a') * q = a * q + a' * q := by ring
  -- either `d·a ≤ q`, or `d·a = q+1` and the remainder is maximal
  have hcase : d * a * a ≤ a * q + r := by
    rcases Nat.lt_or_ge q (d * a) with h | h
    swap
    · have h1 : d * a * a ≤ q * a := Nat.mul_le_mul_right a h
      nlinarith
    · have h1 : d * a * (a + a') ≤ (a + a') * q + r + 1 := by omega
      have h2 : (a + a') * q + r + 1 ≤ (q + 1) * (a + a') := by nlinarith
      have h5 : d * a ≤ q + 1 := Nat.le_of_mul_le_mul_right (by nlinarith) hs
      have hdq : d * a = q + 1 := by omega
      have h6 : (q + 1) * (a + a') ≤ (a + a') * q + r + 1 := by
        rw [← hdq]; exact h1
      have hrs : a + a' ≤ r + 1 := by nlinarith
      have : d * a * a = a * q + a := by rw [hdq]; ring
      omega
  rw [gtBound, min_eq_left]
  refine Nat.succ_le_succ ?_
  rw [Nat.le_div_iff_mul_le (by omega), Nat.sub_sub, Nat.le_sub_iff_add_le hm2]
  nlinarith
