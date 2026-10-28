-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_Ioc_powers_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:38:21.056527+00:00
-- url     : https://prove2.me/submissions/c581cbb9-0969-4071-9751-273c527dc7f0

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_continuous_antitone_L1_powers_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_antitone_positive_kernel_mass_lower_bound
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Translate geometric Ioc convolution-power data into positive-time pointwise decay. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hKL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hKmass : ∀ y : ℝ, 0 ≤ y →
      (∫ t in Ioc (0 : ℝ) y, κ t ∂volume) ≤ ρ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ F n t)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFmass : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in Ioc (0 : ℝ) u, F n s ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by
  have hKmassInt : ∀ y : ℝ, 0 < y →
      (∫ t in (0 : ℝ)..y, κ t) ≤ ρ := by
    intro y hy
    rw [intervalIntegral.integral_of_le hy.le]
    exact hKmass y hy.le
  have hKpoint : ∀ x : ℝ, 0 < x → κ x ≤ ρ / x := by
    intro x hx
    have hint := causal_positive_L1_intervalIntegrable κ hKL1 x hx
    have hlow := antitone_positive_kernel_mass_lower_bound κ hanti x hx hint
    have hmul : x * κ x ≤ ρ := hlow.trans (hKmassInt x hx)
    apply (le_div_iff₀ hx).2
    simpa only [mul_comm] using hmul
  have hFmassInt : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ t in (0 : ℝ)..u, F n t) ≤ ρ ^ (n + 1) := by
    intro n u hu
    rw [intervalIntegral.integral_of_le hu]
    exact hFmass n u hu
  have hstep : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume := by
    intro n x hx
    calc
      F (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume := by
            exact congrFun (hsucc n) x
      _ = ∫ s in Ioc (0 : ℝ) x, F n s * κ (x - s) ∂volume := by
            exact positive_Ioc_causal_convolution_comm_real κ (F n) x hx
      _ = ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume := by
            congr 1
            funext s
            ring
  exact causal_continuous_antitone_L1_powers_quadratic
    κ F ρ hρ hanti hκcont hKpoint hKnonneg hKL1 hKmassInt
    hzero hstep hFnonneg hFL1 hFmassInt
