-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_primitive_geometric_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:38:31.501011+00:00
-- url     : https://prove2.me/submissions/6ede7603-473e-4851-8fc3-9edb85348c13

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exp_scaled_primitive_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_mass_bound
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Weighted signed Gaussian convolution-power primitives have geometric bounds. -/
theorem solution
    (P F : ℕ → ℝ → ℝ) (a w ρ : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1)) :
    ∃ H : ℕ → ℝ → ℝ,
      (∀ n : ℕ, H n = fun x : ℝ =>
        (Real.exp (-w * x) *
          (∫ s in Ioc (0 : ℝ) x,
            Real.exp (w * s) * P n s ∂volume)) / a) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
        ‖H n x‖ ≤ ρ ^ (n + 1) / a) ∧
      (∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ))) := by
  let H : ℕ → ℝ → ℝ := fun n x =>
    (Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P n s ∂volume)) / a
  have hHdef : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x,
          Real.exp (w * s) * P n s ∂volume)) / a := by
    intro n
    rfl
  have hHbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      ‖H n x‖ ≤ ρ ^ (n + 1) / a := by
    intro n x hx
    rcases eq_or_lt_of_le hx with hzero | hxpos
    · subst x
      have hr : 0 ≤ ρ ^ (n + 1) / a :=
        div_nonneg (pow_nonneg hρ0 _) ha.le
      simpa [H] using hr
    · simpa only [Real.norm_eq_abs] using
        (causal_scaled_primitive_mass_bound
          (P n) (F n) a w x (ρ ^ (n + 1)) ha hw hxpos
          (hPL1 n) (hFL1 n) (hDom n) (hFmass n x hx))
  have hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)) := by
    intro n
    exact causal_exp_scaled_primitive_continuous_nonnegative
      (P n) a w hw (hPL1 n)
  exact ⟨H, hHdef, hHbound, hHcont⟩
