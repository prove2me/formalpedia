-- Prove2me | solution 1 for AvramDividend.Classical.atom_zero_of_finite_laplace_inverse_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:37:36.614048+00:00
-- url     : https://prove2.me/submissions/b8211250-c1c1-4530-9295-6d12a3402e14

import Mathlib
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : μ (Iio (0 : ℝ)) = 0)
    (F : ℕ → ℝ) (hF : Tendsto F atTop atTop)
    (hLap : ∀ n : ℕ,
      (∫ x : ℝ, Real.exp ((n : ℝ) * (-x)) ∂μ) = (F n)⁻¹) :
    μ {(0 : ℝ)} = 0 := by
  have hNonneg : ∀ᵐ x ∂μ, 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupport] with x hx
    exact le_of_not_gt (by simpa only [mem_Iio] using hx)
  have hAtom := nonnegative_laplace_transform_atom_zero_limit_nat
    μ (fun x : ℝ => x) measurable_id hNonneg
  have hInv : Tendsto (fun n : ℕ => (F n)⁻¹)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hF
  have hVan : Tendsto
      (fun n : ℕ => ∫ x : ℝ, Real.exp ((n : ℝ) * (-x)) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    convert hInv using 1
    funext n
    exact hLap n
  have hZero : (∫ x : ℝ,
      if x = 0 then (1 : ℝ) else 0 ∂μ) = 0 :=
    tendsto_nhds_unique hAtom hVan
  have hIndicator : (∫ x : ℝ,
      if x = 0 then (1 : ℝ) else 0 ∂μ) =
        μ.real {(0 : ℝ)} := by
    simpa [Set.indicator] using
      (integral_indicator_one (measurableSet_singleton (0 : ℝ)) (μ := μ))
  have hReal : (μ {(0 : ℝ)}).toReal = 0 := by
    simpa only [Measure.real] using (hIndicator.symm.trans hZero)
  rcases (ENNReal.toReal_eq_zero_iff _).mp hReal with hz | ht
  · exact hz
  · exact (measure_ne_top μ {(0 : ℝ)} ht).elim
