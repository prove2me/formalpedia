-- Prove2me | solution 1 for BroughanRH.nicolasPrimeCounting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:19:27.61894+00:00
-- url     : https://prove2.me/submissions/bac7dd5e-d1ee-437f-9d18-2fc725e43f22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_nicolasNormalizedLower
import Mathlib

noncomputable section
open scoped BigOperators

namespace BRHNPC

def expLower (q : ℝ) : ℝ := ∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i : ℝ)

def logLower (q : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range 12, ((q-1)/(q+1)) ^ (2*i+1) / (2*i+1 : ℝ)

lemma logLower_le {q : ℝ} (hq : 1 ≤ q) : logLower q ≤ Real.log q := by
  have hp : 0 < q+1 := by linarith
  have ht₀ : 0 ≤ (q-1)/(q+1) := div_nonneg (by linarith) hp.le
  have ht₁ : (q-1)/(q+1) < 1 := (div_lt_one hp).mpr (by linarith)
  have hid : (1+(q-1)/(q+1))/(1-(q-1)/(q+1)) = q := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div ht₀ ht₁ 12
  rw [hid] at hl
  unfold logLower; linarith

lemma expLower_le {q : ℝ} (hq : 0 ≤ q) : expLower q ≤ Real.exp q :=
  Real.sum_le_exp_of_nonneg hq 30

lemma log_ge (x : ℝ) (k : ℕ) (hx : 2 ^ k ≤ x) :
    k * (0.6931471803 : ℝ) + logLower (x / 2 ^ k) ≤ Real.log x := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hx1 : 1 ≤ x / 2 ^ k := by rw [le_div_iff₀ h2k]; linarith
  have e : Real.log x = k * Real.log 2 + Real.log (x / 2 ^ k) := by
    rw [Real.log_div (by linarith) h2k.ne', Real.log_pow]; ring
  rw [e]
  have := logLower_le hx1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith

lemma LL_ge (x r1 lo : ℝ) (k j : ℕ) (hx : 2 ^ k ≤ x)
    (h1 : r1 ≤ k * (0.6931471803 : ℝ) + logLower (x / 2 ^ k)) (hr1 : 2 ^ j ≤ r1)
    (h2 : lo ≤ j * (0.6931471803 : ℝ) + logLower (r1 / 2 ^ j)) :
    lo ≤ Real.log (Real.log x) := by
  have hr0 : 0 < r1 := lt_of_lt_of_le (by positivity) hr1
  have hlx : r1 ≤ Real.log x := le_trans h1 (log_ge x k hx)
  have := log_ge r1 j hr1
  have := Real.log_le_log hr0 hlx
  linarith

lemma LL_le (x v w : ℝ) (hx : 1 < x) (h1 : x ≤ expLower v) (hv : 0 ≤ v)
    (h2 : v ≤ expLower w) (hw : 0 ≤ w) : Real.log (Real.log x) ≤ w := by
  have hlx : Real.log x ≤ v := by
    rw [Real.log_le_iff_le_exp (by linarith)]; exact le_trans h1 (expLower_le hv)
  have hl0 : 0 < Real.log x := Real.log_pos hx
  calc Real.log (Real.log x) ≤ Real.log v := Real.log_le_log hl0 hlx
    _ ≤ w := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact le_trans h2 (expLower_le hw)

lemma LL_pos (x : ℝ) (hx : 3 ≤ x) : 0 < Real.log (Real.log x) := by
  apply Real.log_pos
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9; linarith

lemma LL_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    Real.log (Real.log x) ≤ Real.log (Real.log y) := by
  have h1 : 0 < Real.log x := Real.log_pos (by linarith)
  exact Real.log_le_log h1 (Real.log_le_log (by linarith) hxy)



set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma li_lower (y Llo mlo : ℝ) (hL0 : 0 < Llo) (hL : Llo ≤ Real.log y) (hm : mlo ≤ Real.log Llo) :
    1 / 2 + mlo + ∑ k ∈ Finset.range 15, Llo ^ (k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) ≤
      Real.eulerMascheroniConstant + Real.log |Real.log y| +
        ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hly : 0 < Real.log y := lt_of_lt_of_le hL0 hL
  rw [abs_of_pos hly]
  have h1 : mlo ≤ Real.log (Real.log y) := le_trans hm (Real.log_le_log hL0 hL)
  set Ly := Real.log y
  have hsum : Summable (fun k : ℕ => Ly^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))) := by
    have hs := (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial Ly)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    have h1' : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hf : (0 : ℝ) < ((k+1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have : 0 ≤ Ly^(k+1) := by positivity
    exact div_le_div_of_nonneg_left this hf (le_mul_of_one_le_left hf.le h1')
  have h2 : ∑ k ∈ Finset.range 15, Llo ^ (k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) ≤
      ∑ k ∈ Finset.range 15, Ly ^ (k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
    apply Finset.sum_le_sum; intro k _
    gcongr
  have h3 := hsum.sum_le_tsum (Finset.range 15) (fun k _ => by positivity)
  linarith


lemma grp0 : (5 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (2310 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (2310 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (2047047 : ℝ) / 1000000 ≤ Real.log (Real.log (2310 : ℝ)) :=
    LL_ge _ ((7745002 : ℝ) / 1000000) _ 11 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (716398 : ℝ) / 1000000 ≤ Real.log ((2047047 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]


lemma grp1 : (6 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (30030 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (30030 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (2333109 : ℝ) / 1000000 ≤ Real.log (Real.log (30030 : ℝ)) :=
    LL_ge _ ((10309952 : ℝ) / 1000000) _ 14 3 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (847201 : ℝ) / 1000000 ≤ Real.log ((2333109 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]


lemma grp2 : (7 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (510510 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (510510 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (2575901 : ℝ) / 1000000 ≤ Real.log (Real.log (510510 : ℝ)) :=
    LL_ge _ ((13143165 : ℝ) / 1000000) _ 18 3 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (946199 : ℝ) / 1000000 ≤ Real.log ((2575901 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]


lemma grp3 : (8 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (9699690 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (9699690 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (2778049 : ℝ) / 1000000 ≤ Real.log (Real.log (9699690 : ℝ)) :=
    LL_ge _ ((16087604 : ℝ) / 1000000) _ 23 4 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (1021748 : ℝ) / 1000000 ≤ Real.log ((2778049 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]


lemma grp4 : (9 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (223092870 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (223092870 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (2956112 : ℝ) / 1000000 ≤ Real.log (Real.log (223092870 : ℝ)) :=
    LL_ge _ ((19223098 : ℝ) / 1000000) _ 27 4 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (1083874 : ℝ) / 1000000 ≤ Real.log ((2956112 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]


lemma grp5 : (10 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (6469693230 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (6469693230 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (3117524 : ℝ) / 1000000 ≤ Real.log (Real.log (6469693230 : ℝ)) :=
    LL_ge _ ((22590394 : ℝ) / 1000000) _ 32 4 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (1137039 : ℝ) / 1000000 ≤ Real.log ((3117524 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]


lemma grp6 : (11 : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (200560490130 : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (200560490130 : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := by
  have hL : (3259033 : ℝ) / 1000000 ≤ Real.log (Real.log (200560490130 : ℝ)) :=
    LL_ge _ ((26024381 : ℝ) / 1000000) _ 37 4 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hm : (1181430 : ℝ) / 1000000 ≤ Real.log ((3259033 : ℝ) / 1000000) :=
    le_trans (by norm_num [logLower, Finset.sum_range_succ]) (log_ge _ 1 (by norm_num))
  have := li_lower _ _ _ (by norm_num) hL hm
  refine lt_of_lt_of_le ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]

end BRHNPC

open BRHNPC in
theorem solution :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    ∀ x : ℝ, 11 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < li (Chebyshev.theta x) := by
  intro li x hx
  rcases lt_or_ge x 37 with h37 | h37
  · rw [Chebyshev.theta_eq_log_primorial]
    obtain ⟨m, hm⟩ : ∃ m, ⌊x⌋₊ = m := ⟨_, rfl⟩
    rw [hm]
    have h11 : 11 ≤ m := by rw [← hm]; exact Nat.le_floor (by exact_mod_cast hx)
    have h36 : m ≤ 36 := by
      rw [← hm]; have := Nat.floor_le (show (0:ℝ) ≤ x by linarith)
      have : (⌊x⌋₊ : ℝ) < 37 := by linarith
      exact_mod_cast (show ⌊x⌋₊ < 37 by exact_mod_cast this) |> Nat.lt_succ_iff.1
    show (Nat.primeCounting m : ℝ) < Real.eulerMascheroniConstant + Real.log |Real.log (Real.log (primorial m : ℝ))| +
      ∑' k : ℕ, (Real.log (Real.log (primorial m : ℝ)))^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    interval_cases m
    · have hp : primorial 11 = 2310 := by decide
      have hc : Nat.primeCounting 11 = 5 := by decide
      rw [hp, hc]; exact_mod_cast grp0
    · have hp : primorial 12 = 2310 := by decide
      have hc : Nat.primeCounting 12 = 5 := by decide
      rw [hp, hc]; exact_mod_cast grp0
    · have hp : primorial 13 = 30030 := by decide
      have hc : Nat.primeCounting 13 = 6 := by decide
      rw [hp, hc]; exact_mod_cast grp1
    · have hp : primorial 14 = 30030 := by decide
      have hc : Nat.primeCounting 14 = 6 := by decide
      rw [hp, hc]; exact_mod_cast grp1
    · have hp : primorial 15 = 30030 := by decide
      have hc : Nat.primeCounting 15 = 6 := by decide
      rw [hp, hc]; exact_mod_cast grp1
    · have hp : primorial 16 = 30030 := by decide
      have hc : Nat.primeCounting 16 = 6 := by decide
      rw [hp, hc]; exact_mod_cast grp1
    · have hp : primorial 17 = 510510 := by decide
      have hc : Nat.primeCounting 17 = 7 := by decide
      rw [hp, hc]; exact_mod_cast grp2
    · have hp : primorial 18 = 510510 := by decide
      have hc : Nat.primeCounting 18 = 7 := by decide
      rw [hp, hc]; exact_mod_cast grp2
    · have hp : primorial 19 = 9699690 := by decide
      have hc : Nat.primeCounting 19 = 8 := by decide
      rw [hp, hc]; exact_mod_cast grp3
    · have hp : primorial 20 = 9699690 := by decide
      have hc : Nat.primeCounting 20 = 8 := by decide
      rw [hp, hc]; exact_mod_cast grp3
    · have hp : primorial 21 = 9699690 := by decide
      have hc : Nat.primeCounting 21 = 8 := by decide
      rw [hp, hc]; exact_mod_cast grp3
    · have hp : primorial 22 = 9699690 := by decide
      have hc : Nat.primeCounting 22 = 8 := by decide
      rw [hp, hc]; exact_mod_cast grp3
    · have hp : primorial 23 = 223092870 := by decide
      have hc : Nat.primeCounting 23 = 9 := by decide
      rw [hp, hc]; exact_mod_cast grp4
    · have hp : primorial 24 = 223092870 := by decide
      have hc : Nat.primeCounting 24 = 9 := by decide
      rw [hp, hc]; exact_mod_cast grp4
    · have hp : primorial 25 = 223092870 := by decide
      have hc : Nat.primeCounting 25 = 9 := by decide
      rw [hp, hc]; exact_mod_cast grp4
    · have hp : primorial 26 = 223092870 := by decide
      have hc : Nat.primeCounting 26 = 9 := by decide
      rw [hp, hc]; exact_mod_cast grp4
    · have hp : primorial 27 = 223092870 := by decide
      have hc : Nat.primeCounting 27 = 9 := by decide
      rw [hp, hc]; exact_mod_cast grp4
    · have hp : primorial 28 = 223092870 := by decide
      have hc : Nat.primeCounting 28 = 9 := by decide
      rw [hp, hc]; exact_mod_cast grp4
    · have hp : primorial 29 = 6469693230 := by decide
      have hc : Nat.primeCounting 29 = 10 := by decide
      rw [hp, hc]; exact_mod_cast grp5
    · have hp : primorial 30 = 6469693230 := by decide
      have hc : Nat.primeCounting 30 = 10 := by decide
      rw [hp, hc]; exact_mod_cast grp5
    · have hp : primorial 31 = 200560490130 := by decide
      have hc : Nat.primeCounting 31 = 11 := by decide
      rw [hp, hc]; exact_mod_cast grp6
    · have hp : primorial 32 = 200560490130 := by decide
      have hc : Nat.primeCounting 32 = 11 := by decide
      rw [hp, hc]; exact_mod_cast grp6
    · have hp : primorial 33 = 200560490130 := by decide
      have hc : Nat.primeCounting 33 = 11 := by decide
      rw [hp, hc]; exact_mod_cast grp6
    · have hp : primorial 34 = 200560490130 := by decide
      have hc : Nat.primeCounting 34 = 11 := by decide
      rw [hp, hc]; exact_mod_cast grp6
    · have hp : primorial 35 = 200560490130 := by decide
      have hc : Nat.primeCounting 35 = 11 := by decide
      rw [hp, hc]; exact_mod_cast grp6
    · have hp : primorial 36 = 200560490130 := by decide
      have hc : Nat.primeCounting 36 = 11 := by decide
      rw [hp, hc]; exact_mod_cast grp6
  · have h := BroughanRH.nicolasNormalizedLower x h37
    simp only at h
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have hl2 := Real.log_two_gt_d9
    have hlpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hpos : 0 < (Real.log x)^2 / Real.sqrt x := by positivity
    by_contra hcon
    push_neg at hcon
    have : (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x ≤ 0 := by
      rw [mul_div_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    linarith
