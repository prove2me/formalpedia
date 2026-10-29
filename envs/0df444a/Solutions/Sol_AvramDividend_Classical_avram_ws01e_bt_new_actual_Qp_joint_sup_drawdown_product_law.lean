-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_actual_Qp_joint_sup_drawdown_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:11:18.116722+00:00
-- url     : https://prove2.me/submissions/bc6d76c9-8baa-4e05-81cd-87066e3efc7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine random-terminal Esscher joint law of the supremum and
drawdown is the product of its two marginal laws. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    let Qp : Measure (Ω × ℝ) :=
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    Measure.map (fun z => (S z, D z)) Qp =
      (Measure.map S Qp).prod (Measure.map D Qp) := by
  classical
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
    (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z =>
    S z - X.X (Real.toNNReal z.2) z.1
  haveI : IsProbabilityMeasure Qp :=
    chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X θ p hθ hp hJoint
  have hS : Measurable S := by
    simpa only [S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D := by
    simpa only [D, S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hInd : IndepFun S D Qp :=
    avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
      X θ p hθ hp hJoint
  change Measure.map (fun z => (S z, D z)) Qp =
    (Measure.map S Qp).prod (Measure.map D Qp)
  exact IndepFun.map_prod_eq_prod_map_map
    hS.aemeasurable hD.aemeasurable hInd
