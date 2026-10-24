-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_convolution_powers_geometric_truncated_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:08:39.430141+00:00
-- url     : https://prove2.me/submissions/d4dd070f-9142-4736-b05e-6ea2bca5d325

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_exact_mass_geometric
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_nonnegative
import Theorems.Thm_AvramDividend_Classical_positive_nonnegative_interval_integral_le_global

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every positive causal power has geometric mass on each initial time interval. -/
theorem solution
    (κ : ℝ → ℝ)
    (hκ : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
        (∫ t in Ioc (0 : ℝ) x, F n t ∂volume) ≤
        (∫ t in Ioi (0 : ℝ), κ t ∂volume) ^ (n + 1)) := by
  obtain ⟨F, hzero, hsucc, hInt, hMass⟩ :=
    AvramDividend.Classical.causal_l1_convolution_power_exact_mass_geometric
      κ hκ
  have hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x :=
    AvramDividend.Classical.causal_Ioc_convolution_powers_nonnegative
      κ F hzero hsucc hκpos
  refine ⟨F, hzero, hsucc, hInt, hpos, ?_⟩
  intro n x hx
  have hineq :=
    AvramDividend.Classical.positive_nonnegative_interval_integral_le_global
      (F n) (hInt n) (fun t ht => hpos n t ht.le) x hx
  rw [hMass n] at hineq
  exact hineq
