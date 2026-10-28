-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_zero_barrier_of_unit_nearfield_and_drift_le_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:29:04.144903+00:00
-- url     : https://prove2.me/submissions/904d0649-71e6-4767-91f4-8ccddbbf34a1

import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_hjb_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- When the Lévy drift is at most the discount rate, only reserves
strictly below one require a separate generator calculation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (hcost : X.c ≤ q)
    (hsmall : ∀ y : ℝ, 0 < y → y < 1 →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  by_cases hy1 : y < 1
  · obtain ⟨hint, hle⟩ := hsmall y hy hy1
    refine ⟨hint, ?_⟩
    rw [vcstar_deriv_eq_one_above_cstar W y (by simpa [hc0] using hy)]
    simpa using (max_eq_right hle)
  · have hge : 1 ≤ y := le_of_not_gt hy1
    have hqy : q ≤ q * y := by
      simpa using (mul_le_mul_of_nonneg_left hge hq.le : q * 1 ≤ q * y)
    exact vcstar_far_field_hjb_zero_barrier X hX q hq W hW hc0 y hge
      (le_trans hcost hqy)
