-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:55:36.208198+00:00
-- url     : https://prove2.me/submissions/e8fdf240-7a35-4aad-91b6-e6480720ad1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine Esscher theorem at theta=0 is the original product-clock law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    ProbabilityTheory.IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      (P.prod (ProbabilityTheory.expMeasure p)) := by
  have hpsi : X.ψ 0 = 0 :=
    AvramDividend.Classical.levy_laplace_exponent_zero X
  have hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp ((0 : ℝ) * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ 0))) := by
    simpa [hpsi] using
      (measurable_const : Measurable (fun _ : Ω × ℝ => (1 : ℝ≥0∞)))
  have h := AvramDividend.Classical.avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
    X 0 p le_rfl hp hJoint
  simpa [hpsi, MeasureTheory.withDensity_one] using h
