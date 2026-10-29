-- Prove2me | solution 2 for AvramDividend.Classical.levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:59:37.823569+00:00
-- url     : https://prove2.me/submissions/a61f038d-9f56-402a-b04d-44d61a375302

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (hD : (P.prod (expMeasure p))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0) :
    (P.prod (expMeasure p))
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} = 0 := by
  have hg : Measurable (fun z : Ω × ℝ => (z.2.toNNReal, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hXm : Measurable (fun z : Ω × ℝ => X.X z.2.toNNReal z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hg
  have hSm : Measurable (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1) :=
    (levy_runningSup_joint_time_path_measurable X).comp hg
  have hIm : Measurable (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp hg
  have h0 : (fun z : Ω × ℝ => X.X 0 z.1) = fun _ => 0 := by funext z; exact X.X_zero z.1
  have h0m : Measurable (fun z : Ω × ℝ => X.X 0 z.1) := by rw [h0]; exact measurable_const
  have hF : Measurable (fun z : Ω × ℝ =>
      (runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1, X.X z.2.toNNReal z.1 - X.X 0 z.1)) :=
    (hSm.sub hXm).prodMk (hXm.sub h0m)
  have hG : Measurable (fun z : Ω × ℝ =>
      (X.X 0 z.1 + -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1},
       X.X z.2.toNNReal z.1 - X.X 0 z.1)) :=
    (h0m.add hIm).prodMk (hXm.sub h0m)
  have hA : MeasurableSet {q : ℝ × ℝ | q.1 = 0} := measurableSet_eq_fun measurable_fst measurable_const
  have hmap := congrArg (fun ν : Measure (ℝ × ℝ) => ν {q : ℝ × ℝ | q.1 = 0})
    (chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a X p hp)
  rw [Measure.map_apply hF hA, Measure.map_apply hG hA] at hmap
  have e : (fun z : Ω × ℝ =>
      (X.X 0 z.1 + -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1},
       X.X z.2.toNNReal z.1 - X.X 0 z.1)) ⁻¹' {q : ℝ × ℝ | q.1 = 0} =
      {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} := by
    ext z; simp [X.X_zero z.1]
  rw [← e, ← hmap]
  exact hD
