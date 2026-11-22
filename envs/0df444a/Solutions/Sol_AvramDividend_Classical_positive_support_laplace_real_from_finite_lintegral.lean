-- Prove2me | solution 1 for AvramDividend.Classical.positive_support_laplace_real_from_finite_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:51:13.951978+00:00
-- url     : https://prove2.me/submissions/ef5b0b0d-992f-42e9-9140-58d9c59b1950

import Mathlib
import Theorems.Thm_AvramDividend_Classical_integral_eq_toReal_lintegral_ofReal_nonneg
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution (U : Measure ℝ) (hIic : U (Iic (0 : ℝ)) = 0)
    (s c : ℝ) (hs : 0 < s) (hc : 0 ≤ c)
    (hLap : (∫⁻ y : ℝ,
      ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
        ENNReal.ofReal c) :
    IntegrableOn (fun y : ℝ => Real.exp (-(s * y))) (Ioi 0) U ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(s * y)) ∂U) = c := by
  let f : ℝ → ℝ := fun y => Real.exp (-(s * y))
  have hMeas : Measurable f := by fun_prop
  have hNonneg : ∀ᵐ y ∂U, 0 ≤ f y :=
    Filter.Eventually.of_forall (fun y => Real.exp_nonneg _)
  have hInt : Integrable f U :=
    (lintegral_ofReal_ne_top_iff_integrable
      hMeas.aestronglyMeasurable hNonneg).mp (by
        change (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) ≠ ⊤
        rw [hLap]
        exact ENNReal.ofReal_ne_top)
  have hReal := integral_eq_toReal_lintegral_ofReal_nonneg U
    f hInt hNonneg
  have hEq : (∫ y : ℝ, f y ∂U) = c := by
    rw [hReal, hLap, ENNReal.toReal_ofReal hc]
  have hAE : ∀ᵐ y ∂U, y ∈ Ioi (0 : ℝ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hIic] with y hy
    exact lt_of_not_ge (by simpa only [mem_Iic] using hy)
  have hRestrict : U.restrict (Ioi (0 : ℝ)) = U :=
    Measure.restrict_eq_self_of_ae_mem hAE
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, hRestrict, f] using hInt
  · simpa only [hRestrict, f] using hEq
