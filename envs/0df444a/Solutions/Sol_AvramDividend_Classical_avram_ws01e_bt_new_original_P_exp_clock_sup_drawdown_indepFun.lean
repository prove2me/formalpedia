-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:24:24.991696+00:00
-- url     : https://prove2.me/submissions/ca22f909-a8d5-491c-8dd3-4b11eb680cb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      (P.prod (expMeasure p)) := by
  have hψ : X.ψ 0 = 0 := by
    simp [SpectrallyNegativeLevy.ψ, laplaceExponent]
  have hd : (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (0 * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ 0))) = fun _ => 1 := by
    funext z; simp [hψ]
  have h1 : (fun _ : Ω × ℝ => (1 : ℝ≥0∞)) = 1 := rfl
  have h := AvramDividend.Classical.avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
    X 0 p le_rfl hp (by rw [hd]; exact measurable_const)
  rw [hd, h1, withDensity_one] at h
  exact h
