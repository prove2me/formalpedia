-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_killed_wh_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:18:22.906994+00:00
-- url     : https://prove2.me/submissions/67a7ebbb-ebd6-4e0b-a4f4-1da299082bab

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- Actual lower-killed scale reward in the original supremum-drawdown joint law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (x q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
      then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞) ∂(P.prod (expMeasure r))) =
    (∫⁻ a : ℝ × ℝ,
      if a.2 ≤ x then ENNReal.ofReal (W (x - a.2 + a.1))
      else (0 : ℝ≥0∞)
      ∂((P.prod (expMeasure r)).map
        (fun z : Ω × ℝ =>
          (runningSup X (Real.toNNReal z.2) z.1,
           runningSup X (Real.toNNReal z.2) z.1 -
             X.X (Real.toNNReal z.2) z.1)))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
  let L : Ω × ℝ → ℝ := fun z =>
    -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}
  let Y : Ω × ℝ → ℝ := fun z =>
    X.X (Real.toNNReal z.2) z.1 + L z
  let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z => S z - X.X (Real.toNNReal z.2) z.1
  let g : ℝ × ℝ → ℝ≥0∞ := fun a =>
    if a.1 ≤ x then ENNReal.ofReal (W (x - a.1 + a.2)) else 0
  let f : ℝ × ℝ → ℝ≥0∞ := fun a =>
    if a.2 ≤ x then ENNReal.ofReal (W (x - a.2 + a.1)) else 0
  have hTime : Measurable (fun z : Ω × ℝ => (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hL : Measurable L := by
    simpa [L, Function.comp_def] using
      (levy_running_infimum_joint_time_path_measurable X).comp hTime
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hTime
  have hLY : Measurable (fun z : Ω × ℝ => (L z, Y z)) :=
    hL.prodMk (hXt.add hL)
  have hYL : Measurable (fun z : Ω × ℝ => (Y z, L z)) :=
    (hXt.add hL).prodMk hL
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hg : Measurable g := Measurable.ite
    (measurableSet_Iic.preimage measurable_fst)
    (ENNReal.measurable_ofReal.comp (hWm.comp
      ((measurable_const.sub measurable_fst).add measurable_snd))) measurable_const
  have hf : Measurable f := Measurable.ite
    (measurableSet_Iic.preimage measurable_snd)
    (ENNReal.measurable_ofReal.comp (hWm.comp
      ((measurable_const.sub measurable_snd).add measurable_fst))) measurable_const
  have hPair : μ.map (fun z => (S z, D z)) =
      μ.map (fun z => (Y z, L z)) := by
    simpa only [μ, S, D, Y, L, X.X_zero, sub_zero, zero_add] using
      (chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a X r hr)
  calc
    _ = ∫⁻ a : ℝ × ℝ, g a ∂(μ.map (fun z => (L z, Y z))) := by
      simpa only [μ, L, Y, g] using
        (chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
          P X r hr x q W hW)
    _ = ∫⁻ a : ℝ × ℝ, f a ∂(μ.map (fun z => (Y z, L z))) := by
      rw [lintegral_map hg hLY, lintegral_map hf hYL]
    _ = ∫⁻ a : ℝ × ℝ, f a ∂(μ.map (fun z => (S z, D z))) := by
      rw [hPair]
