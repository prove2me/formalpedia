-- Prove2me | solution 1 for CountingLLL.DetCount.dyadic_truncation_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:19:39.976734+00:00
-- url     : https://prove2.me/submissions/8833d1fc-161c-4b80-8b17-18eb3b3ead06

import Theorems.Thm_CountingLLL_DetCount_approximation_from_estimator
import Mathlib
set_option autoImplicit false

/-- A logarithmic truncation budget is sufficient at dyadic precision. -/
private theorem truncation_budget (m s : ℕ) :
    let L := 10 * (s + Nat.log2 (m+1) + 6)
    (m : ℝ) * (8 * (0.9 : ℝ)^L) ≤ ((1/2 : ℝ)^s)/4 := by
  dsimp only
  let l := Nat.log2 (m+1)
  let t := s+l+6
  have hbase : (0.9 : ℝ)^10 ≤ 1/2 := by norm_num
  have hpow : (0.9 : ℝ)^(10*t) ≤ (1/2 : ℝ)^t := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hm : (m : ℝ) ≤ (2:ℝ)^(l+1) := by
    have hn : m+1 < 2^((m+1).log2+1) := Nat.lt_log2_self
    have hn' : (m:ℝ) ≤ (2:ℝ)^(l+1) := by exact_mod_cast (by omega : m ≤ 2^((m+1).log2+1))
    exact hn'
  have hcancel : (m:ℝ)*(1/2:ℝ)^l ≤ 2 := by
    have h := mul_le_mul_of_nonneg_right hm (show 0 ≤ (1/2:ℝ)^l by positivity)
    have heq : (2:ℝ)^(l+1)*(1/2:ℝ)^l = 2 := by
      calc
        (2:ℝ)^(l+1)*(1/2:ℝ)^l = ((2:ℝ)^l*(1/2:ℝ)^l)*2 := by rw [pow_succ]; ring
        _ = 2 := by rw [← mul_pow]; norm_num
    rw [heq] at h
    exact h
  have hfactor : (m:ℝ)*8*(1/2:ℝ)^t ≤ (1/2:ℝ)^s/4 := by
    have h := mul_le_mul_of_nonneg_left hcancel (show 0 ≤ (8:ℝ)*(1/2:ℝ)^s/64 by positivity)
    dsimp [t]
    rw [pow_add, pow_add]
    norm_num
    nlinarith
  calc
    (m : ℝ) * (8 * (0.9 : ℝ)^(10*(s+Nat.log2 (m+1)+6)))
        ≤ (m:ℝ)*8*(1/2:ℝ)^t := by
          dsimp [t,l] at hpow ⊢
          nlinarith [mul_nonneg (show 0 ≤ (m:ℝ) by positivity) (sub_nonneg.mpr hpow)]
    _ ≤ (1/2:ℝ)^s/4 := hfactor


open scoped Classical BigOperators
open CountingLLL.DetCount CountingLLL.DetCount.CSP

theorem solution (Φ : CSP) (hΦ : Φ.Condition11)
    (en : Φ.EnumChoice) (hen : Φ.ValidEnum en) (s : ℕ) :
    let ε : ℝ := (1/2)^s
    let L := 10 * (s + Nat.log2 (Φ.m+1) + 6)
    let Cpre : ℕ → Finset (Fin Φ.m) :=
      fun i => Finset.univ.filter (fun j : Fin Φ.m => j.val < i)
    let Zhat : ℝ := (∏ v, (Φ.q v : ℝ)) *
      ∏ i : Fin Φ.m, (1 - Φ.rhatWith en L (Cpre (i.val+1)) i)
    (1-ε)*(Φ.ZPhi : ℝ) ≤ Zhat ∧ Zhat ≤ (1+ε)*(Φ.ZPhi : ℝ) := by
  apply approximation_from_estimator Φ hΦ _ en hen _ (by positivity) ?_ (truncation_budget Φ.m s)
  exact pow_le_one₀ (by norm_num) (by norm_num)
