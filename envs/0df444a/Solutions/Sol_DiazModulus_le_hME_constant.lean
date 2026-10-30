-- Prove2me | solution 1 for DiazModulus.le_hME_constant
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:06:57.094669+00:00
-- url     : https://prove2.me/submissions/69fba103-e74d-4598-a7f1-e394d24edb39

import Mathlib

open Complex ComplexConjugate

/-! # From the Hilbert-side bound to hME's constant

With `d = d₀ + d₁`, the exponent inequality `r·d ≤ d(d+1)/2 + r(r−1)/2` holds for every `r`:
both halves are exact (`d(d+1)` and `r(r−1)` are even) and
`d(d+1) + r(r−1) − 2rd = (d − r)(d − r + 1) ≥ 0`, a product of consecutive integers. So
`2^{rd} ≤ 2^{d(d+1)/2} · 2^{r(r−1)/2}`, and cancelling `2^{r(r−1)/2} > 0` from the hypothesis
gives `λ ≤ 2^{d(d+1)/2} D₀^{d₀} (2D₁)^{d₁} = 2^{d(d+1)/2} 2^{d₁} D₀^{d₀} D₁^{d₁}`. The extra
factors `d!` and `d₀^{d₀}` of hME's constant are at least 1 (`0⁰ = 1`). -/

namespace C11_A5

/-- `r·d ≤ d(d+1)/2 + r(r−1)/2` for all `r, d`. -/
theorem exp_le (r d : ℕ) : r * d ≤ d * (d + 1) / 2 + r * (r - 1) / 2 := by
  have e1 : d * (d + 1) / 2 * 2 = d * (d + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self d))
  have e2 : r * (r - 1) / 2 * 2 = r * (r - 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self r))
  rcases r with _ | s
  · simp
  · simp only [Nat.add_sub_cancel] at e2 ⊢
    have key : 2 * ((s + 1) * d) ≤ d * (d + 1) + (s + 1) * s := by
      zify
      rcases le_or_gt d s with h | h
      · have h' : (0 : ℤ) ≤ (s : ℤ) - d := by omega
        nlinarith [mul_nonneg h' (show (0 : ℤ) ≤ (s : ℤ) + 1 - d by omega)]
      · have h' : (0 : ℤ) ≤ (d : ℤ) - s - 1 := by omega
        nlinarith [mul_nonneg h' (show (0 : ℤ) ≤ (d : ℤ) - s by omega)]
    omega

end C11_A5

open C11_A5 in
theorem solution (lam r d₀ d₁ D₀ D₁ : ℕ)
    (h : lam * 2 ^ (r * (r - 1) / 2) ≤ 2 ^ (r * (d₀ + d₁)) * (D₀ ^ d₀ * (2 * D₁) ^ d₁)) :
    lam ≤ (2 ^ ((d₀ + d₁) * (d₀ + d₁ + 1) / 2) * (d₀ + d₁).factorial * 2 ^ d₁ * d₀ ^ d₀)
      * D₀ ^ d₀ * D₁ ^ d₁ := by
  have hpos : 0 < 2 ^ (r * (r - 1) / 2) := by positivity
  have h2 : lam * 2 ^ (r * (r - 1) / 2) ≤
      (2 ^ ((d₀ + d₁) * (d₀ + d₁ + 1) / 2) * (D₀ ^ d₀ * (2 * D₁) ^ d₁)) * 2 ^ (r * (r - 1) / 2) :=
    calc _ ≤ 2 ^ (r * (d₀ + d₁)) * (D₀ ^ d₀ * (2 * D₁) ^ d₁) := h
      _ ≤ 2 ^ ((d₀ + d₁) * (d₀ + d₁ + 1) / 2 + r * (r - 1) / 2) * (D₀ ^ d₀ * (2 * D₁) ^ d₁) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (exp_le r (d₀ + d₁)))
      _ = _ := by rw [pow_add]; ring
  have h3 := Nat.le_of_mul_le_mul_right h2 hpos
  have hf : 1 ≤ (d₀ + d₁).factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd0 : 1 ≤ d₀ ^ d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h0 | h0
    · simp [h0]
    · exact Nat.one_le_pow _ _ h0
  calc lam ≤ 2 ^ ((d₀ + d₁) * (d₀ + d₁ + 1) / 2) * (D₀ ^ d₀ * (2 * D₁) ^ d₁) := h3
    _ = 2 ^ ((d₀ + d₁) * (d₀ + d₁ + 1) / 2) * 1 * 2 ^ d₁ * 1 * D₀ ^ d₀ * D₁ ^ d₁ := by
        rw [mul_pow]; ring
    _ ≤ _ := by gcongr
