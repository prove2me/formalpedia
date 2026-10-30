-- Prove2me | solution 1 for DiazModulus.params_exponents
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:49.375003+00:00
-- url     : https://prove2.me/submissions/f74427e7-ad1a-4052-8b2b-de79d5f4bc05

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Step 7b of DALAG Th. 11.21: the exponents of a frequent inequality (11.23)

Write `x = S₁`, `L = log x`, `e = d₁/(d₀+d₁−n) ≥ 1`, `F = x^e L^ν`, `N = d₀+d₁`. Along the curve the
floors satisfy `⌊F⌋/N ≥ F/(2N)`, `S₁/N ≥ x/(2N)`, `T₀ ≤ F/L` and `T₁ ≤ F/x` for large `x`, so the left
side is at least `P = (F/(2N))^a (x/(2N))^b` and the right side at most `Q = max(c₈,1)(F/L)^{c₀}(F/x)^{c₁}`.
With `log F = eL + ν log L`, `log P − log Q = −g·L − h·log L − const`, where
`g = e(c₀+c₁−a) − c₁ − b` and `h = ν(c₀+c₁−a) − c₀`. If the conclusion fails, then either `g < 0`
(when `(b+c₁)(d₀+d₁−n) > d₁(c₀+c₁−a)`, or when `a = c₀+c₁` and `b+c₁ > 0`), or `g = 0` and `h = −c₀ < 0`
(when `a = c₀+c₁`, `b = c₁ = 0`, using `1 ≤ c₀+c₁`). In both cases `−g·L − h·log L → ∞`
(`Real.isLittleO_log_id_atTop`), so `Q < P` for all large `S₁`, against the frequent inequality. -/

namespace C14_P2
open DiazModulus Real Filter

theorem growth (g h c : ℝ) (hgh : 0 < g ∨ (g = 0 ∧ 0 < h)) :
    ∀ᶠ x : ℝ in atTop, c < g * Real.log x + h * Real.log (Real.log x) := by
  suffices H : ∀ᶠ y : ℝ in atTop, c < g * y + h * Real.log y from tendsto_log_atTop.eventually H
  rcases hgh with hg | ⟨rfl, hh⟩
  · have hb := Real.isLittleO_log_id_atTop.bound (c := g / (2 * (|h| + 1))) (by positivity)
    filter_upwards [hb, eventually_ge_atTop (2 * |c| / g + 1), eventually_ge_atTop 1]
      with y hy hy1 hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (by linarith : 0 ≤ y)] at hy
    have h1 : -(h * Real.log y) ≤ |h| * |Real.log y| := by rw [← abs_mul]; exact neg_le_abs _
    have h2 : |h| * |Real.log y| ≤ (|h| + 1) * (g / (2 * (|h| + 1)) * y) :=
      mul_le_mul (by linarith) hy (abs_nonneg _) (by positivity)
    have h3 : (|h| + 1) * (g / (2 * (|h| + 1)) * y) = g * y / 2 := by field_simp
    have h4 : g * (2 * |c| / g + 1) ≤ g * y := mul_le_mul_of_nonneg_left hy1 hg.le
    have h5 : g * (2 * |c| / g + 1) = 2 * |c| + g := by field_simp
    have h6 := le_abs_self c
    linarith
  · simp only [zero_mul, zero_add]
    exact (tendsto_log_atTop.eventually_gt_atTop (c / h)).mono fun y hy => by
      rwa [div_lt_iff₀ hh, mul_comm] at hy

theorem natdiv_gt (m N : ℕ) (hN : 0 < N) : (m : ℝ) / N - 1 < ((m / N : ℕ) : ℝ) := by
  have h' : (m : ℝ) < (m / N : ℕ) * N + N := by exact_mod_cast Nat.lt_div_mul_add (a := m) hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_sub_one hN'.ne', div_lt_iff₀ hN']; linarith

theorem main {d0 d1 n : ℕ} (hnd : n < d0 + d1) (hd0n : d0 ≤ n) (ν : ℝ)
    (c8 : ℝ) (a b c0 c1 : ℕ) (S : ℕ) (hxN : 2 * ((d0 : ℝ) + d1) ≤ S) (hx : 2 ≤ (S : ℝ))
    (hL : 1 ≤ Real.log S) (hLν : 4 ≤ Real.log S ^ ν)
    (hfin : Real.log (max c8 1) + ((a : ℝ) + b) * Real.log (2 * ((d0 : ℝ) + d1)) <
      (-((d1 : ℝ) / (d0 + d1 - n) * ((c0 : ℝ) + c1 - a) - c1 - b)) * Real.log S
        + (-(ν * ((c0 : ℝ) + c1 - a) - c0)) * Real.log (Real.log S)) :
    c8 * ((⌊(⌊(S : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S ^ ν⌋₊ : ℝ) / Real.log S⌋₊ : ℕ) : ℝ) ^ c0 * ((⌊(⌊(S : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S ^ ν⌋₊ : ℝ) / S⌋₊ : ℕ) : ℝ) ^ c1
      < ((⌊(S : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S ^ ν⌋₊ / (d0 + d1) : ℕ) : ℝ) ^ a *
          ((S / (d0 + d1) : ℕ) : ℝ) ^ b := by
  have hD : (0 : ℝ) < d0 + d1 - n := by
    have : (n : ℝ) < d0 + d1 := by exact_mod_cast hnd
    linarith
  set e : ℝ := (d1 : ℝ) / (d0 + d1 - n) with he
  have he1 : 1 ≤ e := by
    rw [he, one_le_div hD]
    have : (d0 : ℝ) ≤ n := by exact_mod_cast hd0n
    linarith
  clear_value e
  have hN : 0 < d0 + d1 := by omega
  have hNc : (((d0 + d1 : ℕ)) : ℝ) = (d0 : ℝ) + d1 := by push_cast; ring
  set Nr : ℝ := (d0 : ℝ) + d1 with hNr
  have hNr0 : 0 < Nr := by rw [← hNc]; exact_mod_cast hN
  set x : ℝ := (S : ℝ) with hxdef
  set L := Real.log x with hLdef
  set F := x ^ e * L ^ ν with hFdef
  set T := ⌊F⌋₊ with hTdef
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hLx : L ≤ x := by have := Real.log_le_sub_one_of_pos hx0; linarith
  have hxe : x ≤ x ^ e := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) he1
  have hLν0 : 0 < L ^ ν := Real.rpow_pos_of_pos hL0 ν
  have hF : x * L ^ ν ≤ F := mul_le_mul_of_nonneg_right hxe hLν0.le
  have hF0 : 0 < F := by positivity
  have hF4 : 4 * x ≤ F := by have := mul_le_mul_of_nonneg_left hLν hx0.le; linarith
  have hTle : (T : ℝ) ≤ F := Nat.floor_le hF0.le
  have hTgt : F - 1 < T := by have := Nat.lt_floor_add_one F; linarith
  have hT0le : ((⌊(T : ℝ) / L⌋₊ : ℕ) : ℝ) ≤ F / L :=
    (Nat.floor_le (by positivity)).trans (div_le_div_of_nonneg_right hTle hL0.le)
  have hT1le : ((⌊(T : ℝ) / x⌋₊ : ℕ) : ℝ) ≤ F / x :=
    (Nat.floor_le (by positivity)).trans (div_le_div_of_nonneg_right hTle hx0.le)
  -- lower bounds for the left side of (11.23)
  have hT' : F / (2 * Nr) ≤ ((T / (d0 + d1) : ℕ) : ℝ) := by
    have h1 := natdiv_gt T (d0 + d1) hN
    rw [hNc] at h1
    have h2 : (F - 1) / Nr < T / Nr := div_lt_div_of_pos_right hTgt hNr0
    have h3 : (F - 1) / Nr - 1 - F / (2 * Nr) = (F - 2 - 2 * Nr) / (2 * Nr) := by
      field_simp; ring
    have h4 : 0 ≤ (F - 2 - 2 * Nr) / (2 * Nr) := div_nonneg (by linarith) (by positivity)
    linarith
  have hs : x / (2 * Nr) ≤ ((S / (d0 + d1) : ℕ) : ℝ) := by
    have h1 := natdiv_gt S (d0 + d1) hN
    rw [hNc] at h1
    have h3 : x / Nr - 1 - x / (2 * Nr) = (x - 2 * Nr) / (2 * Nr) := by field_simp; ring
    have h4 : 0 ≤ (x - 2 * Nr) / (2 * Nr) := div_nonneg (by linarith) (by positivity)
    linarith
  set c8' := max c8 1 with hc8'
  have hc8'0 : 0 < c8' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set P := (F / (2 * Nr)) ^ a * (x / (2 * Nr)) ^ b with hP
  set Q := c8' * ((F / L) ^ c0 * (F / x) ^ c1) with hQ
  have hPle : P ≤ ((T / (d0 + d1) : ℕ) : ℝ) ^ a * ((S / (d0 + d1) : ℕ) : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hT' _) (pow_le_pow_left₀ (by positivity) hs _)
      (by positivity) (by positivity)
  have hQge : c8 * ((⌊(T : ℝ) / L⌋₊ : ℕ) : ℝ) ^ c0 * ((⌊(T : ℝ) / x⌋₊ : ℕ) : ℝ) ^ c1 ≤ Q := by
    rw [mul_assoc]
    calc _ ≤ c8' * (((⌊(T : ℝ) / L⌋₊ : ℕ) : ℝ) ^ c0 * ((⌊(T : ℝ) / x⌋₊ : ℕ) : ℝ) ^ c1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ Q := mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (by positivity) hT0le _)
          (pow_le_pow_left₀ (by positivity) hT1le _) (by positivity) (by positivity)) hc8'0.le
  refine lt_of_le_of_lt hQge (lt_of_lt_of_le ?_ hPle)
  have hlogF : Real.log F = e * L + ν * Real.log L := by
    rw [hFdef, Real.log_mul (Real.rpow_pos_of_pos hx0 e).ne' hLν0.ne', Real.log_rpow hx0,
      Real.log_rpow hL0]
  have hQl : Real.log Q = Real.log c8' + (c0 * (Real.log F - Real.log L) + c1 * (Real.log F - L)) := by
    rw [hQ, Real.log_mul hc8'0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_div hF0.ne' hL0.ne', Real.log_div hF0.ne' hx0.ne']
  have hPl : Real.log P = a * (Real.log F - Real.log (2 * Nr)) + b * (L - Real.log (2 * Nr)) := by
    rw [hP, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div hF0.ne' (by positivity), Real.log_div hx0.ne' (by positivity)]
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), hQl, hPl, hlogF]
  linear_combination hfin
end C14_P2

open DiazModulus C14_P2 in
theorem solution {d0 d1 n : ℕ} (hnd : n < d0 + d1) (hd0n : d0 ≤ n)
    (ν : ℝ) (hν0 : 0 < ν) (c8 : ℝ) (a b c0 c1 : ℕ) (hd' : 1 ≤ c0 + c1) (ha : a ≤ c0 + c1)
    (hfreq : ∃ᶠ S₁ : ℕ in Filter.atTop,
      ((⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ / (d0 + d1) : ℕ) : ℝ) ^ a *
          ((S₁ / (d0 + d1) : ℕ) : ℝ) ^ b
        ≤ c8 * ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / Real.log S₁⌋₊ : ℕ) : ℝ) ^ c0 * ((⌊(⌊(S₁ : ℝ) ^ ((d1 : ℝ) / (d0 + d1 - n)) * Real.log S₁ ^ ν⌋₊ : ℝ) / S₁⌋₊ : ℕ) : ℝ) ^ c1) :
    a < c0 + c1 ∧ (b + c1) * (d0 + d1 - n) ≤ d1 * (c0 + c1 - a) := by
  by_contra hcon
  have hD : (0 : ℝ) < d0 + d1 - n := by
    have : (n : ℝ) < d0 + d1 := by exact_mod_cast hnd
    linarith
  set e : ℝ := (d1 : ℝ) / (d0 + d1 - n) with he
  have heD : e * ((d0 : ℝ) + d1 - n) = d1 := by rw [he]; field_simp
  clear_value e
  have key : 0 < -(e * ((c0 : ℝ) + c1 - a) - c1 - b) ∨
      (-(e * ((c0 : ℝ) + c1 - a) - c1 - b) = 0 ∧ 0 < -(ν * ((c0 : ℝ) + c1 - a) - c0)) := by
    by_cases hac : a < c0 + c1
    · left
      have hnot : ¬ (b + c1) * (d0 + d1 - n) ≤ d1 * (c0 + c1 - a) := fun h => hcon ⟨hac, h⟩
      push Not at hnot
      have hc : (d1 : ℝ) * ((c0 : ℝ) + c1 - a) < ((b : ℝ) + c1) * ((d0 : ℝ) + d1 - n) := by
        have := (Nat.cast_lt (α := ℝ)).2 hnot
        push_cast [Nat.cast_sub hac.le, Nat.cast_sub hnd.le] at this
        linarith
      have h1 : (-(e * ((c0 : ℝ) + c1 - a) - c1 - b)) * ((d0 : ℝ) + d1 - n)
          = ((b : ℝ) + c1) * ((d0 : ℝ) + d1 - n) - d1 * ((c0 : ℝ) + c1 - a) := by
        linear_combination (-((c0 : ℝ) + c1 - a)) * heD
      have h2 : 0 * ((d0 : ℝ) + d1 - n) < (-(e * ((c0 : ℝ) + c1 - a) - c1 - b)) * ((d0 : ℝ) + d1 - n) := by
        rw [h1, zero_mul]; linarith
      exact lt_of_mul_lt_mul_right h2 hD.le
    · have ha' : a = c0 + c1 := le_antisymm ha (not_lt.1 hac)
      have h0 : ((c0 : ℝ) + c1 - a) = 0 := by rw [ha']; push_cast; ring
      rw [h0]
      by_cases hbc : b + c1 = 0
      · right
        have hc1 : c1 = 0 := by omega
        have hb0 : b = 0 := by omega
        have hc0 : (1 : ℝ) ≤ c0 := by exact_mod_cast (by omega : 1 ≤ c0)
        subst hc1 hb0
        constructor
        · simp
        · simp; linarith
      · left
        have : (0 : ℝ) < b + c1 := by exact_mod_cast Nat.pos_of_ne_zero hbc
        simp; linarith
  have hlog := Real.tendsto_log_atTop
  have e0 := growth _ _ (Real.log (max c8 1) + ((a : ℝ) + b) * Real.log (2 * ((d0 : ℝ) + d1))) key
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, 2 * ((d0 : ℝ) + d1) ≤ x := Filter.eventually_ge_atTop _
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x := Filter.eventually_ge_atTop 2
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ Real.log x := hlog.eventually_ge_atTop 1
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ Real.log x ^ ν :=
    ((tendsto_rpow_atTop hν0).comp hlog).eventually_ge_atTop 4
  have evN := tendsto_natCast_atTop_atTop.eventually (e0.and (e1.and (e2.and (e3.and e4))))
  obtain ⟨S, hS1, hS2⟩ := (hfreq.and_eventually evN).exists
  obtain ⟨h0, h1, h2, h3, h4⟩ := hS2
  rw [he] at h0 hS1
  have := main hnd hd0n ν c8 a b c0 c1 S h1 h2 h3 h4 h0
  linarith
