-- Prove2me | solution 1 for BroughanRH.matiyasevichWitness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:02:38.111017+00:00
-- url     : https://prove2.me/submissions/d24d22f2-23cd-4cd0-ba68-bee4c28ac4a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_schoenfeldPsi
import Mathlib

namespace BRHMatW

/-- `log (x+1) - log x ≤ 1/x` and `≥ 1/(x+1)`. -/
lemma log_succ_sub_le (x : ℝ) (hx : 0 < x) : Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [← Real.log_div (by linarith) hx.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

lemma log_succ_sub_ge (x : ℝ) (hx : 0 < x) : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  rw [← Real.log_div (by linarith) hx.ne']
  have := Real.one_sub_inv_le_log_of_pos (show 0 < (x + 1) / x by positivity)
  have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
  linarith

/-- From `(a+1) x^(xb) < 4 (x+1)^(xb)`: `log (a+1) < log 4 + b`. -/
lemma lower_of (a b x : ℕ) (hx : 0 < x)
    (h : (a+1)*x^(x*b) < 4*(x+1)^(x*b)) : Real.log (a + 1) < Real.log 4 + b := by
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have h' : ((a : ℝ) + 1) * (x : ℝ) ^ (x * b) < 4 * ((x : ℝ) + 1) ^ (x * b) := by exact_mod_cast h
  have hl := Real.log_lt_log (by positivity) h'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hl
  have hs := log_succ_sub_le x hxr
  have hxb : (0 : ℝ) ≤ ((x * b : ℕ) : ℝ) := by positivity
  have : ((x * b : ℕ) : ℝ) * (Real.log (x + 1) - Real.log x) ≤ b := by
    calc ((x * b : ℕ) : ℝ) * (Real.log (x + 1) - Real.log x) ≤ ((x * b : ℕ) : ℝ) * (1 / x) := by
          gcongr
      _ = b := by push_cast; field_simp
  nlinarith

/-- From `(x+1)^(xb) ≤ (a+1) x^(xb)` and `b+1 < x`: `b < log (a+1) + 1`. -/
lemma upper_of (a b x : ℕ) (hbx : b + 1 < x)
    (h : (x+1)^(x*b) ≤ (a+1)*x^(x*b)) : (b : ℝ) < Real.log (a + 1) + 1 := by
  have hx : 0 < x := by omega
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have h' : ((x : ℝ) + 1) ^ (x * b) ≤ ((a : ℝ) + 1) * (x : ℝ) ^ (x * b) := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) h'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
  have hs := log_succ_sub_ge x hxr
  set L := Real.log ((a : ℝ) + 1) with hL
  have hkey : ((x * b : ℕ) : ℝ) * (1 / (x + 1)) ≤ L := by
    have : ((x * b : ℕ) : ℝ) * (1 / ((x : ℝ) + 1)) ≤ ((x * b : ℕ) : ℝ) * (Real.log (x + 1) - Real.log x) := by
      gcongr
    linarith
  push_cast at hkey
  have hbx' : (b : ℝ) + 1 < x := by exact_mod_cast hbx
  by_contra hcon
  push_neg at hcon
  -- b x ≤ L (x+1), with L + 1 ≤ b and b + 1 < x
  have h2 : (x : ℝ) * b ≤ L * (x + 1) := by
    have := hkey; rw [mul_one_div, div_le_iff₀ (by positivity)] at this; linarith
  nlinarith

end BRHMatW

open BRHMatW in
theorem solution :
    let M (a b : ℕ) := ∃ x : ℕ, b+1 < x ∧
      (x+1)^(x*b) ≤ (a+1)*x^(x*b) ∧ (a+1)*x^(x*b) < 4*(x+1)^(x*b)
    ¬ ∃ k l m n : ℕ, 0 < k ∧ 0 < l ∧ 600 ≤ n ∧
      m = (Finset.Icc 1 n).lcm id ∧
      (4*n*k^4 : ℕ) < (Int.natAbs ((l : ℤ) - (n : ℤ)))^2 ∧
      M (m-1) l ∧ M (n-1) k := by
  intro M
  rintro ⟨k, l, m, n, hk, hl, hn, hm, hineq, ⟨x, hx1, hx2, hx3⟩, ⟨y, hy1, hy2, hy3⟩⟩
  have hm0 : 0 < m := by rw [hm]; exact Nat.lcmUpto_pos n
  have hm1 : m - 1 + 1 = m := by omega
  have hn1 : n - 1 + 1 = n := by omega
  rw [hm1] at hx2 hx3
  rw [hn1] at hy2 hy3
  -- l ≈ ψ(n), k ≳ log n
  have hpsi : Chebyshev.psi n = Real.log m := by
    rw [Chebyshev.psi_eq_log_lcmUpto, hm]; rfl
  have hl_lo := lower_of (m-1) l x (by omega) (by rw [hm1]; exact hx3)
  have hl_hi := upper_of (m-1) l x hx1 (by rw [hm1]; exact hx2)
  have hk_lo := lower_of (n-1) k y (by omega) (by rw [hn1]; exact hy3)
  have hm1r : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm1
  have hn1r : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn1
  rw [hm1r, ← hpsi] at hl_lo hl_hi
  rw [hn1r] at hk_lo
  -- constants
  have hnr : (600 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hLn : 6 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have h1 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 6 < (2.7182818286 : ℝ) ^ 6 := by
      gcongr
    norm_num at h3; rw [h1]; linarith
  -- Schoenfeld
  have hS := BroughanRH.schoenfeldPsi n (by norm_num; linarith)
  set L := Real.log (n : ℝ) with hL
  set s := Real.sqrt (n : ℝ) with hs
  have hs0 : 24 ≤ s := by
    rw [hs, show (24 : ℝ) = Real.sqrt (24^2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hss : s * s = n := Real.mul_self_sqrt (by linarith)
  have hpi : (24 : ℝ) < 8 * Real.pi := by linarith [Real.pi_gt_three]
  -- |l - n| bound
  have hlr : |(l : ℝ) - n| < s * L ^ 2 / (8 * Real.pi) + 2 := by
    have := abs_sub_lt_iff.1 hS
    rw [abs_sub_lt_iff]; constructor <;> linarith
  have hSL : s * L ^ 2 / (8 * Real.pi) ≤ s * L ^ 2 / 24 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hpi.le
  -- k bound
  have hkL : L - 2 * Real.log 2 < k := by linarith
  have hk4 : (L - 2) ^ 4 ≤ (k : ℝ) ^ 4 := by
    apply pow_le_pow_left₀ (by linarith); linarith
  -- the inequality in ℝ
  have hineqR : (4 * n * k ^ 4 : ℝ) < ((l : ℝ) - n) ^ 2 := by
    have h := hineq
    have : ((4*n*k^4 : ℕ) : ℝ) < (((Int.natAbs ((l : ℤ) - (n : ℤ)))^2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    have e : ((Int.natAbs ((l : ℤ) - (n : ℤ)) : ℕ) : ℝ) = |(l : ℝ) - n| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [e, sq_abs] at this; exact this
  -- contradiction: (l-n)^2 < (sL^2/24 + 2)^2 ≤ 4 n (L-2)^4
  have hA : ((l : ℝ) - n) ^ 2 < (s * L ^ 2 / 24 + 2) ^ 2 := by
    rw [← sq_abs]; apply pow_lt_pow_left₀ (by linarith) (abs_nonneg _) (by norm_num)
  have hB : (s * L ^ 2 / 24 + 2) ^ 2 ≤ 4 * n * (L - 2) ^ 4 := by
    rw [← hss]
    have hL6 : 6 ≤ L := hLn.le
    have h3 : 4 * L ^ 2 / 9 ≤ (L - 2) ^ 2 := by
      have : 2 * L / 3 ≤ L - 2 := by linarith
      have h0 : 0 ≤ 2 * L / 3 := by linarith
      calc 4 * L ^ 2 / 9 = (2 * L / 3) ^ 2 := by ring
        _ ≤ (L - 2) ^ 2 := pow_le_pow_left₀ h0 this 2
    have hL2 : 36 ≤ L ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 6) hL6 2; norm_num at this; linarith
    have h4 : 24 * 36 ≤ s * L ^ 2 := mul_le_mul hs0 hL2 (by norm_num) (by linarith)
    have h5 : s * (4 * L ^ 2 / 9) ≤ s * (L - 2) ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
    have e1 : s * (4 * L ^ 2 / 9) = 4 / 9 * (s * L ^ 2) := by ring
    have e2 : 2 * s * (L - 2) ^ 2 = 2 * (s * (L - 2) ^ 2) := by ring
    have e3 : s * L ^ 2 / 24 = 1 / 24 * (s * L ^ 2) := by ring
    have h1 : s * L ^ 2 / 24 + 2 ≤ 2 * s * (L - 2) ^ 2 := by
      rw [e2, e3]; rw [e1] at h5; linarith
    have h0 : 0 ≤ s * L ^ 2 / 24 + 2 := by positivity
    calc (s * L ^ 2 / 24 + 2) ^ 2 ≤ (2 * s * (L - 2) ^ 2) ^ 2 := by gcongr
      _ = 4 * (s * s) * (L - 2) ^ 4 := by ring
  have hC : 4 * (n : ℝ) * (L - 2) ^ 4 ≤ 4 * n * k ^ 4 := by
    have : (0 : ℝ) ≤ 4 * n := by positivity
    exact mul_le_mul_of_nonneg_left hk4 this
  linarith
