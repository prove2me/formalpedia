-- Prove2me | solution 1 for DiazModulus.params_1122_eventually
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:45.802743+00:00
-- url     : https://prove2.me/submissions/4988c998-a4a9-4d31-b4ab-664d466f7a99

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Step 7a of DALAG Th. 11.21: the parameter constraint holds for all large `S₁`

Write `x = S₁`, `L = log x`, `e = d₁/(d₀+d₁−n) ≥ 1`, `F = x^e L^ν`, `S₀ = ⌊F⌋`, `T₀ = ⌊S₀/L⌋`,
`T₁ = ⌊S₀/x⌋`. Since `ν > 0` and `e ≥ 1`, `F ≥ x L^ν`, so `F/x ≥ L^ν → ∞`; the floors then give
`T₀ ≥ F/(2L)` and `T₁ ≥ F/(2x)`, both `≥ 2`, and `T₀ ≤ F/L`, `T₁ ≤ F/x`. The left side is at most
`K·F·L` with `K = C(6+e+ν)`, using `log(T₀+T₁+2) ≤ log(3F) ≤ (2+e+ν)L`, `log(x+2) ≤ 2L` and `x+1 ≤ 2x`.
The right side is at least `G^{1/n}` with `G = (F/(2L))^{d₀}(F/x)^{d₁}`. Comparing logarithms, with
`log F = eL + ν log L`, the coefficient of `L` is `(e(d₀+d₁−n) − d₁)/n = 0` and the coefficient of
`log L` is `((d₀+d₁−n)ν − d₀ − n)/n > 0`, so the inequality holds once `log log x` is large. The
real statement is pulled back to `ℕ` along `Nat.cast`. -/

namespace C14_P1
open DiazModulus Real Filter

theorem main {d0 d1 n : ℕ} (hn : 1 ≤ n) (hnd : n < d0 + d1) (hd0n : d0 ≤ n)
    (C : ℝ) (hC : 0 < C) (ν : ℝ) (hν0 : 0 < ν) (x : ℝ) (hx : 2 ≤ x) (hL : 1 ≤ Real.log x)
    (hLν : 4 ≤ Real.log x ^ ν)
    (hll : (d0 : ℝ) * Real.log 2 + n * Real.log (C * (6 + (d1 : ℝ) / (d0 + d1 - n) + ν))
      ≤ (((d0 : ℝ) + d1 - n) * ν - d0 - n) * Real.log (Real.log x)) :
      2 ≤ ⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / Real.log x⌋₊ ∧
      2 ≤ ⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / x⌋₊ ∧
      C * (((⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℕ) : ℝ) * Real.log (((⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / Real.log x⌋₊ : ℕ) : ℝ)
            + ((⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / x⌋₊ : ℕ) : ℝ) + 2)
          + ((⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / Real.log x⌋₊ : ℕ) : ℝ) * Real.log (x + 2)
          + ((⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / x⌋₊ : ℕ) : ℝ) * (x + 1))
        ≤ ((((⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / Real.log x⌋₊) + 1) ^ d0 * (2 * (⌊(⌊x ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log x ^ ν⌋₊ : ℝ) / x⌋₊) + 1) ^ d1 : ℕ) : ℝ)
            ^ ((1 : ℝ) / n) := by
  have hD : (0 : ℝ) < d0 + d1 - n := by
    have : (n : ℝ) < d0 + d1 := by exact_mod_cast hnd
    linarith
  set e : ℝ := (d1 : ℝ) / (d0 + d1 - n) with he
  have heD : e * ((d0 : ℝ) + d1 - n) = d1 := by rw [he]; field_simp
  have he1 : 1 ≤ e := by
    rw [he, one_le_div hD]
    have : (d0 : ℝ) ≤ n := by exact_mod_cast hd0n
    linarith
  clear_value e
  set L := Real.log x with hLdef
  set F := x ^ e * L ^ ν with hFdef
  set T := ⌊F⌋₊ with hTdef
  set T0 := ⌊(T : ℝ) / L⌋₊ with hT0def
  set T1 := ⌊(T : ℝ) / x⌋₊ with hT1def
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hLx : L ≤ x := by have := Real.log_le_sub_one_of_pos hx0; linarith
  have hxe : x ≤ x ^ e := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) he1
  have hLν0 : 0 < L ^ ν := Real.rpow_pos_of_pos hL0 ν
  have hF : x * L ^ ν ≤ F := mul_le_mul_of_nonneg_right hxe hLν0.le
  have hF0 : 0 < F := by positivity
  have hFx : 4 ≤ F / x := by
    rw [le_div_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hLν hx0.le
    linarith
  have hFxL : F / x ≤ F / L := div_le_div_of_nonneg_left hF0.le hL0 hLx
  have hTle : (T : ℝ) ≤ F := Nat.floor_le hF0.le
  have hTgt : F - 1 < T := by have := Nat.lt_floor_add_one F; linarith
  have hT0le : (T0 : ℝ) ≤ F / L :=
    (Nat.floor_le (by positivity)).trans (div_le_div_of_nonneg_right hTle hL0.le)
  have hT1le : (T1 : ℝ) ≤ F / x :=
    (Nat.floor_le (by positivity)).trans (div_le_div_of_nonneg_right hTle hx0.le)
  have hT0gt : F / L - 2 < T0 := by
    have h1 := Nat.lt_floor_add_one ((T : ℝ) / L)
    have h2 : (F - 1) / L < T / L := div_lt_div_of_pos_right hTgt hL0
    have h3 : (F - 1) / L = F / L - 1 / L := sub_div _ _ _
    have h4 : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL
    rw [← hT0def] at h1; linarith
  have hT1gt : F / x - 2 < T1 := by
    have h1 := Nat.lt_floor_add_one ((T : ℝ) / x)
    have h2 : (F - 1) / x < T / x := div_lt_div_of_pos_right hTgt hx0
    have h3 : (F - 1) / x = F / x - 1 / x := sub_div _ _ _
    have h4 : 1 / x ≤ 1 := by rw [div_le_one hx0]; linarith
    rw [← hT1def] at h1; linarith
  have hT0 : F / L / 2 ≤ T0 := by linarith
  have hT1 : F / x / 2 ≤ T1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (2 : ℝ) ≤ T0 := by linarith
    exact_mod_cast this
  · have : (2 : ℝ) ≤ T1 := by linarith
    exact_mod_cast this
  -- the logarithm of `F`
  have hlogF : Real.log F = e * L + ν * Real.log L := by
    rw [hFdef, Real.log_mul (Real.rpow_pos_of_pos hx0 e).ne' hLν0.ne', Real.log_rpow hx0,
      Real.log_rpow hL0]
  have hlL : Real.log L ≤ L := by have := Real.log_le_sub_one_of_pos hL0; linarith
  have hFL : F / L ≤ F := div_le_self hF0.le hL
  have hFx' : F / x ≤ F := div_le_self hF0.le (by linarith)
  -- upper bound for the left side
  set K := C * (6 + e + ν) with hK
  have hK0 : 0 < K := by positivity
  have hp1 : (T : ℝ) * Real.log ((T0 : ℝ) + T1 + 2) ≤ F * ((2 + e + ν) * L) := by
    have hpos : (0 : ℝ) < T0 + T1 + 2 := by positivity
    have hle : (T0 : ℝ) + T1 + 2 ≤ 3 * F := by linarith
    have hlog : Real.log ((T0 : ℝ) + T1 + 2) ≤ (2 + e + ν) * L := by
      have h1 := Real.log_le_log hpos hle
      rw [Real.log_mul (by norm_num) hF0.ne', hlogF] at h1
      have h3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
      have h4 : ν * Real.log L ≤ ν * L := mul_le_mul_of_nonneg_left hlL hν0.le
      linear_combination h1 + h3 + h4 + 2 * hL
    exact mul_le_mul hTle hlog (Real.log_nonneg (by linarith)) hF0.le
  have hp2 : (T0 : ℝ) * Real.log (x + 2) ≤ 2 * F := by
    have hlog : Real.log (x + 2) ≤ 2 * L := by
      have h1 := Real.log_le_log (by linarith) (by
        linear_combination mul_nonneg (sub_nonneg.2 hx) (by linarith : (0 : ℝ) ≤ x + 1) :
          x + 2 ≤ x ^ 2)
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    calc (T0 : ℝ) * Real.log (x + 2) ≤ F / L * (2 * L) :=
          mul_le_mul hT0le hlog (Real.log_nonneg (by linarith)) (by positivity)
      _ = 2 * F := by field_simp
  have hp3 : (T1 : ℝ) * (x + 1) ≤ 2 * F := by
    calc (T1 : ℝ) * (x + 1) ≤ F / x * (2 * x) :=
          mul_le_mul hT1le (by linarith) (by linarith) (by positivity)
      _ = 2 * F := by field_simp
  have hLHS : C * ((T : ℝ) * Real.log ((T0 : ℝ) + T1 + 2) + T0 * Real.log (x + 2)
      + T1 * (x + 1)) ≤ K * F * L := by
    have hFL1 : F ≤ F * L := le_mul_of_one_le_right hF0.le hL
    have hin : (T : ℝ) * Real.log ((T0 : ℝ) + T1 + 2) + T0 * Real.log (x + 2) + T1 * (x + 1)
        ≤ (6 + e + ν) * F * L := by linear_combination hp1 + hp2 + hp3 + 4 * hFL1
    calc _ ≤ C * ((6 + e + ν) * F * L) := mul_le_mul_of_nonneg_left hin hC.le
      _ = K * F * L := by rw [hK]; ring
  -- lower bound for the right side
  set G := (F / L / 2) ^ d0 * (F / x) ^ d1 with hG
  have hG0 : 0 < G := by positivity
  have hGle : G ≤ ((((T0 + 1) ^ d0 * (2 * T1 + 1) ^ d1 : ℕ)) : ℝ) := by
    push_cast
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine hLHS.trans (le_trans ?_ (Real.rpow_le_rpow hG0.le hGle (by positivity)))
  have h1 : Real.log (K * F * L) = Real.log K + Real.log F + Real.log L := by
    rw [Real.log_mul (mul_pos hK0 hF0).ne' hL0.ne', Real.log_mul hK0.ne' hF0.ne']
  have h2 : Real.log G = d0 * (Real.log F - Real.log L - Real.log 2) + d1 * (Real.log F - L) := by
    rw [hG, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div (by positivity) (by norm_num), Real.log_div hF0.ne' hL0.ne',
      Real.log_div hF0.ne' hx0.ne']
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hG0, h1, h2, hlogF,
    one_div, inv_mul_eq_div, le_div_iff₀ hn0]
  linear_combination hll - L * heD
end C14_P1

open DiazModulus C14_P1 in
theorem solution {d0 d1 n : ℕ} (hn : 1 ≤ n) (hnd : n < d0 + d1) (hd0n : d0 ≤ n)
    (C : ℝ) (hC : 0 < C) (ν : ℝ) (hν : ((d0 : ℝ) + n) / ((d0 : ℝ) + d1 - n) < ν) :
    ∀ᶠ S₁ : ℕ in Filter.atTop,
      2 ≤ ⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ ∧
      2 ≤ ⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ ∧
      C * (((⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℕ) : ℝ) * Real.log (((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ)
            + ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) + 2)
          + ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ) * Real.log ((S₁ : ℝ) + 2)
          + ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) * ((S₁ : ℝ) + 1))
        ≤ ((((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊) + 1) ^ d0 * (2 * (⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊) + 1) ^ d1 : ℕ) : ℝ)
            ^ ((1 : ℝ) / n) := by
  have hD : (0 : ℝ) < d0 + d1 - n := by
    have : (n : ℝ) < d0 + d1 := by exact_mod_cast hnd
    linarith
  have hν0 : 0 < ν := lt_of_le_of_lt (by positivity) hν
  have hβ : 0 < ((d0 : ℝ) + d1 - n) * ν - d0 - n := by
    rw [div_lt_iff₀ hD] at hν; linarith
  have hlog := Real.tendsto_log_atTop
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x := Filter.eventually_ge_atTop 2
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ Real.log x := hlog.eventually_ge_atTop 1
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ Real.log x ^ ν :=
    ((tendsto_rpow_atTop hν0).comp hlog).eventually_ge_atTop 4
  have e4 : ∀ᶠ x : ℝ in Filter.atTop,
      ((d0 : ℝ) * Real.log 2 + n * Real.log (C * (6 + (d1 : ℝ) / (d0 + d1 - n) + ν))) /
        (((d0 : ℝ) + d1 - n) * ν - d0 - n) ≤ Real.log (Real.log x) :=
    (hlog.comp hlog).eventually_ge_atTop _
  have key : ∀ᶠ x : ℝ in Filter.atTop, _ := (e1.and (e2.and (e3.and e4))).mono
    fun x ⟨h1, h2, h3, h4⟩ => main hn hnd hd0n C hC ν hν0 x h1 h2 h3
      (by rw [div_le_iff₀ hβ] at h4; linarith)
  exact tendsto_natCast_atTop_atTop.eventually key
