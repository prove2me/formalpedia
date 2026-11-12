-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_masked_original_discounted_mark_rate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:33:05.78482+00:00
-- url     : https://prove2.me/submissions/8fff5edd-e050-4446-b8c2-c1d635a0d9f2

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original discounted closed-cap mark kernel has a Borel time mask. -/
theorem solution
    (C τ : ℝ≥0∞) (q T : ℝ) (n : ℕ)
    (U : ℝ≥0 → ℝ) (hU : Measurable U)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then Real.exp (-(q * (t : ℝ))) * ψ (U t)
      else 0) := by
  classical
  have hR : Measurable (fun t : ℝ≥0 => (t : ℝ)) :=
    measurable_coe_nnreal_real
  have hE : Measurable (fun t : ℝ≥0 => (t : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal
  have hUE : Measurable (fun t : ℝ≥0 => ENNReal.ofReal (U t)) :=
    ENNReal.measurable_ofReal.comp hU
  have h1 : MeasurableSet {t : ℝ≥0 | 0 < t} := measurableSet_Ioi
  have h2 : MeasurableSet
      {t : ℝ≥0 | (t : ℝ) < T - T / ((n : ℝ) + 2)} :=
    measurableSet_Iio.preimage hR
  have h3 : MeasurableSet {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ} :=
    measurableSet_Iic.preimage hE
  have h4 : MeasurableSet {t : ℝ≥0 | 0 ≤ U t} :=
    measurableSet_Ici.preimage hU
  have h5 : MeasurableSet {t : ℝ≥0 | ENNReal.ofReal (U t) ≤ C} :=
    measurableSet_Iic.preimage hUE
  have hB : MeasurableSet {t : ℝ≥0 |
      0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C} :=
    h1.inter (h2.inter (h3.inter (h4.inter h5)))
  have hValue : Measurable (fun t : ℝ≥0 =>
      Real.exp (-(q * (t : ℝ))) * ψ (U t)) := by
    fun_prop
  exact hValue.ite hB measurable_const
