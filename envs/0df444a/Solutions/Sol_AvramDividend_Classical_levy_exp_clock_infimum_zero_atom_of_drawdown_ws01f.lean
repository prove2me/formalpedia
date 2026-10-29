-- Prove2me | solution 1 for AvramDividend.Classical.levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:56:22.713832+00:00
-- url     : https://prove2.me/submissions/897c1083-faf8-4355-bc05-738243aede3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
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
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let F : Ω × ℝ → ℝ × ℝ := fun z =>
    (runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1,
      X.X z.2.toNNReal z.1 - X.X 0 z.1)
  let G : Ω × ℝ → ℝ × ℝ := fun z =>
    (X.X 0 z.1 + -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ z.2.toNNReal ∧ y = X.X s z.1},
      X.X z.2.toNNReal z.1 - X.X 0 z.1)
  have hPair : Measurable (fun z : Ω × ℝ => (z.2.toNNReal, z.1)) := by fun_prop
  have hState : Measurable (fun z : Ω × ℝ => X.X z.2.toNNReal z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hPair
  have hSup : Measurable (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1) :=
    (levy_runningSup_joint_time_path_measurable X).comp hPair
  have hInf : Measurable (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp hPair
  have hZero : Measurable (fun z : Ω × ℝ => X.X 0 z.1) := by
    simpa only [X.X_zero] using
      (measurable_const : Measurable (fun _ : Ω × ℝ => (0 : ℝ)))
  have hRest : Measurable (fun z : Ω × ℝ =>
      X.X z.2.toNNReal z.1 - X.X 0 z.1) := hState.sub hZero
  have hF : Measurable F := (hSup.sub hState).prodMk hRest
  have hG : Measurable G := (hZero.add hInf).prodMk hRest
  have hS : MeasurableSet {w : ℝ × ℝ | w.1 = 0} :=
    (measurable_fst : Measurable (fun w : ℝ × ℝ => w.1))
      (measurableSet_singleton 0)
  have hRev : Measure.map F μ = Measure.map G μ := by
    exact chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a X p hp
  have hEq := congrArg (fun ν : Measure (ℝ × ℝ) =>
      ν {w : ℝ × ℝ | w.1 = 0}) hRev
  rw [Measure.map_apply hF hS, Measure.map_apply hG hS] at hEq
  have hInfEq : μ {z : Ω × ℝ |
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} =
      μ {z : Ω × ℝ |
        runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1 = 0} := by
    simpa only [Set.preimage, Set.mem_setOf_eq, F, G, X.X_zero, zero_add] using hEq.symm
  exact hInfEq.trans hD
