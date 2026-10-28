-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:10:47.553054+00:00
-- url     : https://prove2.me/submissions/18cb0120-a000-416d-9f7c-bb36a7fcaf93

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- The true killed q-scale payoff at an independent exponential time equals
    integration against the genuine reflected-infimum/drawdown pair law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (x q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
      then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞) ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    (∫⁻ a : ℝ × ℝ,
      if a.1 ≤ x then ENNReal.ofReal (W (x - a.1 + a.2))
      else (0 : ℝ≥0∞)
      ∂((P.prod (ProbabilityTheory.expMeasure r)).map
        (fun z : Ω × ℝ =>
          (-sInf {y : ℝ | ∃ s : ℝ≥0,
                    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
           X.X (Real.toNNReal z.2) z.1 +
             -sInf {y : ℝ | ∃ s : ℝ≥0,
                       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) := by
  classical
  let L : Ω × ℝ → ℝ := fun z =>
    -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}
  let Y : Ω × ℝ → ℝ := fun z =>
    X.X (Real.toNNReal z.2) z.1 + L z
  let F : Ω × ℝ → ℝ × ℝ := fun z => (L z, Y z)
  let g : ℝ × ℝ → ℝ≥0∞ := fun a =>
    if a.1 ≤ x then ENNReal.ofReal (W (x - a.1 + a.2)) else 0
  have hTime : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hL : Measurable L := by
    simpa [L, Function.comp_def] using
      (levy_running_infimum_joint_time_path_measurable X).comp hTime
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hTime
  have hF : Measurable F := hL.prodMk (hXt.add hL)
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hReal : Measurable (fun a : ℝ × ℝ =>
      W (x - a.1 + a.2)) :=
    hWm.comp ((measurable_const.sub measurable_fst).add measurable_snd)
  have hCond : MeasurableSet {a : ℝ × ℝ | a.1 ≤ x} :=
    measurableSet_Iic.preimage measurable_fst
  have hg : Measurable g :=
    Measurable.ite hCond (ENNReal.measurable_ofReal.comp hReal) measurable_const
  change (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
      then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞) ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    (∫⁻ a, g a ∂((P.prod (ProbabilityTheory.expMeasure r)).map F))
  rw [lintegral_map hg hF]
  apply lintegral_congr
  intro z
  have hSurv :=
    chat04_reflected_infimum_Iic_iff_survival X (Real.toNNReal z.2) z.1 x
  by_cases hs : ∀ s : ℝ≥0,
      s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
  · have hle : L z ≤ x := hSurv.mpr hs
    simp only [if_pos hs, g, F, if_pos hle]
    congr 1
    dsimp [Y]
    ring
  · have hnle : ¬ L z ≤ x := by
      intro hle
      exact hs (hSurv.mp hle)
    simp only [if_neg hs, g, F, if_neg hnle]
