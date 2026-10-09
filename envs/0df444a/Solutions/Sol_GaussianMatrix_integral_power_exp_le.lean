-- Prove2me | solution 1 for GaussianMatrix.integral_power_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:29:22.595047+00:00
-- url     : https://prove2.me/submissions/27969583-ce54-4778-b5f2-eacd6f566cfe

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

theorem solution {a : ℝ} (ha : -1 < a) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioc 0 t) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) ha)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 this
  calc ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2))
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        apply ENNReal.ofReal_le_ofReal
        have h1 : 0 ≤ x ^ a := Real.rpow_nonneg hx.1.le _
        have h2 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hx.1])
        nlinarith
    _ = ENNReal.ofReal (∫ x in Set.Ioc 0 t, x ^ a) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact Real.rpow_nonneg hx.1.le _
    _ = ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by
        rw [← intervalIntegral.integral_of_le ht, integral_rpow (Or.inl ha),
          Real.zero_rpow (by linarith), sub_zero]
