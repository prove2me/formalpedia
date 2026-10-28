-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_neumann_power_weighted_primitive_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:48:21.250575+00:00
-- url     : https://prove2.me/submissions/ab0188be-e788-453a-9a5b-cc404c67598b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exponential_positive_L1_integrableOn_Ioc
import Theorems.Thm_AvramDividend_Classical_causal_weighted_neumann_primitive_step_local_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every signed causal power obeys the weighted primitive recurrence on finite horizons. -/
theorem solution
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ) (w : ℝ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, Real.exp (w * t) * P (n + 1) t ∂volume) =
      (∫ s in Ioc (0 : ℝ) x,
        (Real.exp (w * (x - s)) * k (x - s)) *
          (∫ t in Ioc (0 : ℝ) s,
            Real.exp (w * t) * P n t ∂volume) ∂volume) := by
  intro n x hx
  have hk := causal_exponential_positive_L1_integrableOn_Ioc
    k w x hkL1 hx
  have hp := causal_exponential_positive_L1_integrableOn_Ioc
    (P n) w x (hPL1 n) hx
  calc
    (∫ t in Ioc (0 : ℝ) x, Real.exp (w * t) * P (n + 1) t ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) *
          (∫ s in Ioc (0 : ℝ) t, k s * P n (t - s) ∂volume) ∂volume) := by
            rw [hPrec n]
    _ = ∫ s in Ioc (0 : ℝ) x,
      (Real.exp (w * (x - s)) * k (x - s)) *
        (∫ t in Ioc (0 : ℝ) s,
          Real.exp (w * t) * P n t ∂volume) ∂volume :=
      causal_weighted_neumann_primitive_step_local_L1 k (P n) w x hx hk hp
