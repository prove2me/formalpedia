-- Prove2me | solution 1 for EntFunctional.toReal_klDiv_withDensity_eq_integral_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T03:53:43.664601+00:00
-- url     : https://prove2.me/submissions/8ac6f2d8-687f-451e-afb3-087262b97402

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Real MeasureTheory
open scoped ENNReal NNReal

theorem solution
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ}
    (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_int : Integrable g μ) (hg_mass : ∫ x, g x ∂μ = 1) :
    (InformationTheory.klDiv (μ.withDensity (fun x ↦ ENNReal.ofReal (g x))) μ).toReal
      = ∫ x, g x * log (g x) ∂μ := by
  set Q : Measure α := μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) with hQ
  have hQmeas : Measurable (fun x ↦ ENNReal.ofReal (g x)) :=
    ENNReal.measurable_ofReal.comp hg_meas
  have hQuniv : Q Set.univ = 1 := by
    rw [hQ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nonneg)]
    rw [hg_mass, ENNReal.ofReal_one]
  haveI : IsProbabilityMeasure Q := ⟨hQuniv⟩
  have hac : Q ≪ μ := by rw [hQ]; exact withDensity_absolutelyContinuous _ _
  have hmass : Q Set.univ = μ Set.univ := by rw [hQuniv, measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac hmass]
  have hrn : Q.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (g x) := by
    rw [hQ]; exact Measure.rnDeriv_withDensity μ hQmeas
  have hllr_mu : (fun x ↦ llr Q μ x) =ᵐ[μ] fun x ↦ log (g x) := by
    filter_upwards [hrn] with x hx
    simp only [llr, hx, ENNReal.toReal_ofReal (hg_nonneg x)]
  have hllr_Q : (fun x ↦ llr Q μ x) =ᵐ[Q] fun x ↦ log (g x) := hac.ae_le hllr_mu
  rw [integral_congr_ae hllr_Q]
  rw [hQ]
  rw [integral_withDensity_eq_integral_toReal_smul hQmeas
      (ae_of_all _ (fun x ↦ ENNReal.ofReal_lt_top)) (fun x ↦ log (g x))]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hg_nonneg x)]
