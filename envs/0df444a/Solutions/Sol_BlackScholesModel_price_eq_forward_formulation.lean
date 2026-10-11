-- Prove2me | solution 1 for BlackScholesModel.price_eq_forward_formulation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:34:27.235738+00:00
-- url     : https://prove2.me/submissions/8f6f5f24-fc28-4539-982c-dcea8df8cb03

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ) (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    callPrice K r σ T S t
        = callPriceFwd (Real.exp (-r * (T - t))) (Real.exp (r * (T - t)) * S) K σ (T - t) ∧
    putPrice K r σ T S t
        = putPriceFwd (Real.exp (-r * (T - t))) (Real.exp (r * (T - t)) * S) K σ (T - t) := by
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hlog :
      Real.log ((Real.exp (r * (T - t)) * S) / K) =
        r * (T - t) + Real.log (S / K) := by
    have hdiv : (Real.exp (r * (T - t)) * S) / K =
        Real.exp (r * (T - t)) * (S / K) := by ring
    rw [hdiv, Real.log_mul (Real.exp_ne_zero _) (div_ne_zero hS0 hK0),
        Real.log_exp]
  have hPlus :
      dPlusFwd (Real.exp (r * (T - t)) * S) K σ (T - t) =
        dPlus S K r σ (T - t) := by
    simp only [dPlusFwd, dPlus]
    rw [hlog]
    congr 1
    ring
  have hMinus :
      dMinusFwd (Real.exp (r * (T - t)) * S) K σ (T - t) =
        dMinus S K r σ (T - t) := by
    simp only [dMinusFwd, dMinus, hPlus]
  have hCancel : Real.exp (-r * (T - t)) * Real.exp (r * (T - t)) = 1 := by
    rw [← Real.exp_add]
    have hz : -r * (T - t) + r * (T - t) = 0 := by ring
    rw [hz]
    simp
  constructor
  · unfold callPrice callPriceFwd
    rw [hPlus, hMinus]
    calc
      _ = (Real.exp (-r * (T - t)) * Real.exp (r * (T - t))) *
          (stdNormalCDF (dPlus S K r σ (T - t)) * S) -
          stdNormalCDF (dMinus S K r σ (T - t)) * K * Real.exp (-r * (T - t)) := by
            rw [hCancel]
            ring
      _ = Real.exp (-r * (T - t)) *
          (stdNormalCDF (dPlus S K r σ (T - t)) *
             (Real.exp (r * (T - t)) * S) -
           stdNormalCDF (dMinus S K r σ (T - t)) * K) := by ring
  · unfold putPrice putPriceFwd
    rw [hPlus, hMinus]
    calc
      _ = stdNormalCDF (-dMinus S K r σ (T - t)) * K * Real.exp (-r * (T - t)) -
          (Real.exp (-r * (T - t)) * Real.exp (r * (T - t))) *
            (stdNormalCDF (-dPlus S K r σ (T - t)) * S) := by
              rw [hCancel]
              ring
      _ = Real.exp (-r * (T - t)) *
          (stdNormalCDF (-dMinus S K r σ (T - t)) * K -
           stdNormalCDF (-dPlus S K r σ (T - t)) *
             (Real.exp (r * (T - t)) * S)) := by ring
