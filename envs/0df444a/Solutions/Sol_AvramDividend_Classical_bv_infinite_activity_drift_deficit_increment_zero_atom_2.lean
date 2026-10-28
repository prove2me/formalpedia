-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:36:06.292566+00:00
-- url     : https://prove2.me/submissions/55ae42b0-8444-4a52-b2f7-4628498f8cea

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (s t : ℝ≥0) (hst : s < t) :
    P.real {ω : Ω |
        (X.drift * (t : ℝ) - X.X t ω) -
          (X.drift * (s : ℝ) - X.X s ω) = 0} = 0 := by
  have hid := actual_levy_drift_deficit_stationary_increment_law X s t hst.le
  have h0 := bv_infinite_activity_drift_deficit_zero_atom X hBV hνinf (t - s) (tsub_pos_of_lt hst)
  have e1 : {ω : Ω | (X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω) = 0} =
      (fun ω => (X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω)) ⁻¹' {0} := rfl
  have e2 : {ω : Ω | (((t - s : ℝ≥0)) : ℝ) * X.drift - X.X (t - s) ω = 0} =
      (fun ω => X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t - s) ω) ⁻¹' {0} := by
    ext ω; simp [mul_comm]
  rw [e2] at h0
  rw [e1, measureReal_def, hid.measure_mem_eq (measurableSet_singleton 0), ← measureReal_def, h0]
