-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:08:00.277739+00:00
-- url     : https://prove2.me/submissions/7a5301fe-bf48-4a06-a28e-cad445335962

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_truncated_clock_only_loses_horizon_endpoint
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact finite-horizon payment set decomposition into the truncated
    strict clock plus whatever original payment occurs at the endpoint. -/
theorem solution
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes σ ∩ Iic T =
      (paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T) ∪
        ((paymentTimes σ ∩ Iic T) ∩ {T}) := by
  apply Set.Subset.antisymm
  · intro t ht
    rcases avram_wave7_11_truncated_clock_only_loses_horizon_endpoint
      σ T hT ht with hclock | hend
    · exact Or.inl hclock
    · exact Or.inr ⟨ht, hend⟩
  · intro t ht
    rcases ht with hclock | hend
    · have hpay : t ∈ paymentTimes (min σ (ENNReal.ofReal T)) := hclock.1
      have hnonneg : 0 ≤ t := hpay.1
      have hor : t = 0 ∨ ENNReal.ofReal t < min σ (ENNReal.ofReal T) := hpay.2
      refine ⟨?_, hclock.2⟩
      change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)
      refine ⟨hnonneg, ?_⟩
      rcases hor with hz | hlt
      · exact Or.inl hz
      · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
    · exact hend.1
