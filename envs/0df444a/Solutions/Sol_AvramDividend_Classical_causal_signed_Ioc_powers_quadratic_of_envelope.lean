-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_Ioc_powers_quadratic_of_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:49:25.728985+00:00
-- url     : https://prove2.me/submissions/5edbffbf-3f69-4654-a488-9a67c9d64b7d

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_signed_convolution_powers_abs_le_envelope
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Pointwise geometric control transfers to signed Ioc powers. -/
theorem solution
    (k κ : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hk : ∀ t : ℝ, 0 < t → |k t| ≤ κ t)
    (hκ : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hP0 : P 0 = k) (hF0 : F 0 = κ)
    (hPsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hFsucc : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hPint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => k (x - s) * P n s) volume 0 x)
    (hFint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by
  have hPs : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      P (n + 1) x = ∫ s in (0 : ℝ)..x, k (x - s) * P n s := by
    intro n x hx
    calc
      P (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume :=
        hPsucc n x hx
      _ = ∫ s in Ioc (0 : ℝ) x, P n s * k (x - s) ∂volume :=
        positive_Ioc_causal_convolution_comm_real k (P n) x hx.le
      _ = ∫ s in Ioc (0 : ℝ) x, k (x - s) * P n s ∂volume := by
        congr 1
        funext s
        ring
      _ = ∫ s in (0 : ℝ)..x, k (x - s) * P n s :=
        (intervalIntegral.integral_of_le hx.le).symm
  have hFs : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F (n + 1) x = ∫ s in (0 : ℝ)..x, κ (x - s) * F n s := by
    intro n x hx
    calc
      F (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume :=
        hFsucc n x hx
      _ = ∫ s in Ioc (0 : ℝ) x, F n s * κ (x - s) ∂volume :=
        positive_Ioc_causal_convolution_comm_real κ (F n) x hx.le
      _ = ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume := by
        congr 1
        funext s
        ring
      _ = ∫ s in (0 : ℝ)..x, κ (x - s) * F n s :=
        (intervalIntegral.integral_of_le hx.le).symm
  have hdom :=
    causal_signed_convolution_powers_abs_le_envelope
      k κ P F hk hκ hP0 hF0 hPs hFs hPint hFint
  intro n x hx
  exact (hdom n x hx).trans (hFpoint n x hx)
