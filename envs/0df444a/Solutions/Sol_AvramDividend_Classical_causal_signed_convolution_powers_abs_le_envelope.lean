-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_convolution_powers_abs_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:57:18.798716+00:00
-- url     : https://prove2.me/submissions/199d6d36-6ab3-44d7-a2c7-6143f48082fb

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_integral_abs_le_majorant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (k κ : ℝ → ℝ) (P F : ℕ → ℝ → ℝ)
    (hk : ∀ t : ℝ, 0 < t → |k t| ≤ κ t)
    (hκ : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hP0 : P 0 = k) (hF0 : F 0 = κ)
    (hPsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x = ∫ s in (0 : ℝ)..x, k (x - s) * P n s)
    (hFsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x = ∫ s in (0 : ℝ)..x, κ (x - s) * F n s)
    (hPint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => k (x - s) * P n s) volume 0 x)
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x → |P n x| ≤ F n x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa [hP0, hF0] using hk x hx
  | succ n ih =>
      intro x hx
      rw [hPsucc n x hx, hFsucc n x hx]
      apply causal_signed_convolution_integral_abs_le_majorant
        k κ (P n) (F n) x hx (hPint n x hx) (hFint n x hx)
      · intro s hs
        exact hk (x - s) (sub_pos.mpr hs.2)
      · intro s hs
        exact ih s hs.1
      · intro s hs
        exact hκ (x - s) (sub_pos.mpr hs.2)
