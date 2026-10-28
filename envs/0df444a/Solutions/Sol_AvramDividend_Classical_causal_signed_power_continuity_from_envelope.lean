-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_power_continuity_from_envelope
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:55:18.117669+00:00
-- url     : https://prove2.me/submissions/c0e46316-7598-4ab9-9d0b-1dfff63b01cd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support
import Theorems.Thm_AvramDividend_Classical_causal_signed_L1_convolution_powers_continuous_positive

open MeasureTheory Set

theorem solution
    (k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hP0 : P 0 = k)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ)) := by
  have hPzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → P n x = 0 := by
    intro n x hx
    cases n with
    | zero => rw [hP0]; exact hkzero x hx
    | succ n =>
      rw [hPrec n]
      simp only
      rw [Ioc_eq_empty (not_lt.mpr hx), Measure.restrict_empty, integral_zero_measure]
  have hbound : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |P n x| ≤ M := by
    intro n ε hε
    refine ⟨((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / ε, fun x hx => ?_⟩
    have hx0 : 0 < x := lt_of_lt_of_le hε hx
    refine (hDom n x hx0.le).trans ((hFpoint n x hx0).trans ?_)
    exact div_le_div_of_nonneg_left (by positivity) hε hx
  refine AvramDividend.Classical.causal_signed_L1_convolution_powers_continuous_positive k P
    (AvramDividend.Classical.causal_positive_l1_global_integrable k hkL1 hkzero) hkcont hkzero
    (fun ε hε => by simpa [hP0] using hbound 0 ε hε) hP0 (fun n => ?_)
    (fun n => AvramDividend.Classical.causal_positive_l1_global_integrable (P n) (hPL1 n)
      (hPzero n)) hPzero hbound
  rw [hPrec n]
  funext x
  exact (AvramDividend.Classical.causal_real_convolution_equals_positive_interval_under_support
    k (P n) hkzero (hPzero n) x).symm
