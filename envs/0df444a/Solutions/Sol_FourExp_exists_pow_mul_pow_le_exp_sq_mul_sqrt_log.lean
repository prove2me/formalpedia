-- Prove2me | solution 1 for FourExp.exists_pow_mul_pow_le_exp_sq_mul_sqrt_log
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:44:37.675978+00:00
-- url     : https://prove2.me/submissions/577d8faf-0315-436b-a855-59d3cd1411d8

import Mathlib

namespace S7W3_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log

/-- `log x ≥ 1` for `x ≥ 3`, since `e < 3`. -/
lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x :=
  (Real.log_exp 1).symm.le.trans
    (Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hx))

/-- The exponent estimate in real variables. Let `s ≥ 1` with `s² = log n` and `s ≤ n`, and let
`m ≤ S`, `S s ≤ n²`, `T ≤ r n`, `a s ≤ r n` and `b ≤ r n s`. Then `(1 + m + S) s ≤ 3 n²`,
`T (a + b) ≤ 2 r² n² s` and `1 + m + S + T + a + b ≤ (3 + 3 r) n²`, so that
`log (1 + m + S + T + a + b) ≤ log (3 + 3 r) + 2 s²`, and the logarithm
`c (1 + m + S + T (a + b)) log c + c (1 + m + S) log (1 + m + S + T + a + b)` of the size bound
is at most `(c (3 + 2 r²) log c + 3 c (log (3 + 3 r) + 2)) n² s`. -/
lemma exponent_le (c r n s S T a b m : ℝ) (hc : 1 ≤ c) (hr : 0 ≤ r) (hn : 1 ≤ n)
    (hs : 1 ≤ s) (hss : s * s = Real.log n) (hsn : s ≤ n)
    (hS0 : 0 ≤ S) (hT0 : 0 ≤ T) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hm0 : 0 ≤ m)
    (hS : S * s ≤ n ^ 2) (hmS : m ≤ S) (hT : T ≤ r * n) (ha : a * s ≤ r * n)
    (hb : b ≤ r * (n * s)) :
    c * (1 + m + S + T * (a + b)) * Real.log c +
        c * (1 + m + S) * Real.log (1 + m + S + T + a + b) ≤
      (c * (3 + 2 * r ^ 2) * Real.log c + 3 * c * (Real.log (3 + 3 * r) + 2)) * (n ^ 2 * s) := by
  have hs0 : 0 ≤ s := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hnn : n * 1 ≤ n * n := mul_le_mul_of_nonneg_left hn hn0
  have hZ0 : 0 ≤ 1 + m + S := by linarith
  have hrn : 0 ≤ r * n := mul_nonneg hr hn0
  -- `(1 + m + S) s ≤ 3 n²`, hence `1 + m + S ≤ 3 n² ≤ 3 n² s`
  have hZs : (1 + m + S) * s ≤ 3 * n ^ 2 := by
    linarith only [mul_le_mul_of_nonneg_right hmS hs0, hS, hsn, hnn]
  have hZ : 1 + m + S ≤ 3 * n ^ 2 := by
    linarith only [hZs, mul_le_mul_of_nonneg_left hs hZ0]
  have hP : n ^ 2 * 1 ≤ n ^ 2 * s := mul_le_mul_of_nonneg_left hs (pow_nonneg hn0 2)
  have hZP : 1 + m + S ≤ 3 * (n ^ 2 * s) := by linarith only [hZ, hP]
  -- `a ≤ r n`, and `T (a + b) ≤ r² n² + r² n² s ≤ 2 r² n² s`
  have ha1 : a ≤ r * n := by linarith only [ha, mul_le_mul_of_nonneg_left hs ha0]
  have hTab : T * (a + b) ≤ 2 * r ^ 2 * (n ^ 2 * s) := by
    linarith only [mul_le_mul_of_nonneg_right hT ha0, mul_le_mul_of_nonneg_left ha1 hrn,
      mul_le_mul_of_nonneg_left hs (mul_nonneg hrn hrn), mul_le_mul_of_nonneg_right hT hb0,
      mul_le_mul_of_nonneg_left hb hrn]
  have hX : 1 + m + S + T * (a + b) ≤ (3 + 2 * r ^ 2) * (n ^ 2 * s) := by
    linarith only [hZP, hTab]
  -- `1 + m + S + T + a + b ≤ (3 + 3 r) n²`, since `r n ≤ r n²` and `r n s ≤ r n²`
  have hY : 1 + m + S + T + a + b ≤ (3 + 3 * r) * n ^ 2 := by
    linarith only [hZ, hT, ha1, hb, mul_le_mul_of_nonneg_left hnn hr,
      mul_le_mul_of_nonneg_left hsn hrn]
  have hY0 : 0 < 1 + m + S + T + a + b := by linarith
  have h3r : 0 < 3 + 3 * r := by linarith
  have hlogY : Real.log (1 + m + S + T + a + b) ≤ Real.log (3 + 3 * r) + 2 * (s * s) := by
    calc Real.log (1 + m + S + T + a + b) ≤ Real.log ((3 + 3 * r) * n ^ 2) :=
          Real.log_le_log hY0 hY
      _ = Real.log (3 + 3 * r) + 2 * (s * s) := by
          rw [Real.log_mul h3r.ne' (pow_pos (by linarith) 2).ne', Real.log_pow, hss,
            Nat.cast_ofNat]
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlr : 0 ≤ Real.log (3 + 3 * r) := Real.log_nonneg (by linarith)
  -- `c X log c ≤ c (3 + 2 r²) n² s log c`, `c Z log(3 + 3 r) ≤ 3 c n² s log(3 + 3 r)` and
  -- `2 c Z s² ≤ 6 c n² s`, with `Z = 1 + m + S`
  linarith only [mul_le_mul_of_nonneg_left hX (mul_nonneg hc0 hlc),
    mul_le_mul_of_nonneg_left hlogY (mul_nonneg hc0 hZ0),
    mul_le_mul_of_nonneg_left hZP (mul_nonneg hc0 hlr),
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZs hs0) hc0]

end S7W3_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log

open S7W3_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log in
/-- The size bound at the scale `N² √(log N)`. For `c = 0` the left side is `1`. For `c ≥ 1`
write it as `exp (c (1 + m + S + T (a + b)) log c + c (1 + m + S) log (1 + m + S + T + a + b))`
and apply `exponent_le` with `s = √(log N)`, which satisfies `1 ≤ s`, `s² = log N` and
`s ≤ log N ≤ N`; the exponent `κ` is `c (3 + 2 r²) log c + 3 c (log (3 + 3 r) + 2) + 1`. -/
theorem solution (c r : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N S T a b m : ℕ, 3 ≤ N →
      (S : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)) → m ≤ S → T ≤ r * N →
      (a : ℝ) ≤ r * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) →
      (b : ℝ) ≤ r * ((N : ℝ) * Real.sqrt (Real.log (N : ℝ))) →
      ((c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) : ℕ) : ℝ)
        ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · -- for `c = 0` the left side is `1`
    refine ⟨1, one_pos, fun N S T a b m _ _ _ _ _ _ => ?_⟩
    simp only [zero_mul, pow_zero, mul_one, one_mul, Nat.cast_one]
    exact Real.one_le_exp (by positivity)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hκ1 : 0 ≤ (c : ℝ) * (3 + 2 * (r : ℝ) ^ 2) * Real.log c :=
    mul_nonneg (by positivity) (Real.log_nonneg hc1)
  have hκ2 : 0 ≤ 3 * (c : ℝ) * (Real.log (3 + 3 * (r : ℝ)) + 2) :=
    mul_nonneg (by positivity) (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 + 3 * r)])
  refine ⟨(c : ℝ) * (3 + 2 * (r : ℝ) ^ 2) * Real.log c + 3 * (c : ℝ) *
      (Real.log (3 + 3 * (r : ℝ)) + 2) + 1, by linarith only [hκ1, hκ2],
    fun N S T a b m hN hS hmS hT ha hb => ?_⟩
  -- the parameter `s = √(log N)`
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log (N : ℝ) := one_le_log_of_three_le hN3
  have hLN : Real.log (N : ℝ) ≤ N := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)]
  have hs1 : 1 ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt hL1)
  have hss : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) = Real.log N :=
    Real.mul_self_sqrt (by linarith)
  generalize Real.sqrt (Real.log (N : ℝ)) = s at hs1 hss hS ha hb ⊢
  have hs0 : 0 < s := by linarith
  have hsn : s ≤ N := by linarith only [mul_le_mul_of_nonneg_left hs1 hs0.le, hss, hLN]
  rw [le_div_iff₀ hs0] at hS
  rw [← mul_div_assoc, le_div_iff₀ hs0] at ha
  have hT' : (T : ℝ) ≤ r * N := by exact_mod_cast hT
  have hmS' : (m : ℝ) ≤ S := by exact_mod_cast hmS
  have key := exponent_le (c : ℝ) r N s S T a b m hc1 hr0 (by linarith) hs1 hss hsn
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hS hmS' hT' ha hb
  -- the left side as an exponential
  have hc0 : (0 : ℝ) < c := by linarith
  have hY0 : (0 : ℝ) < ((1 + m + S + T + a + b : ℕ) : ℝ) := by positivity
  have hLHS : ((c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))
      : ℕ) : ℝ) = Real.exp (((c * (1 + m + S + T * (a + b)) : ℕ) : ℝ) * Real.log c +
        ((c * (1 + m + S) : ℕ) : ℝ) * Real.log ((1 + m + S + T + a + b : ℕ) : ℝ)) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hc0, Real.exp_log hY0,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  rw [hLHS, Real.exp_le_exp]
  push_cast
  linarith only [key, mul_nonneg (pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 2) hs0.le]

#print axioms solution
