-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:48:16.193627+00:00
-- url     : https://prove2.me/submissions/9eb2e755-9dc2-4742-a9cc-c60ce924c463

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      H z.1 z.2))
    (W : Ω → ℝ≥0∞) (hW : Measurable W) :
    Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp
        (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
       H (Real.toNNReal z.2)
         (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1))) := by
  have hY : Measurable (fun ω : Ω => fun s : ℝ≥0 =>
    X.X (τ ω + s) ω - X.X (τ ω) ω) :=
    avram_ws01e_b_randomAge_whole_shiftedPath_measurable X τ hτ
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hu : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) := by
    fun_prop
  have hτz : Measurable (fun z : Ω × ℝ => τ z.1) :=
    hτ.comp measurable_fst
  have hAtStop : Measurable
      (fun z : Ω × ℝ => X.X (τ z.1) z.1) :=
    hX.comp (hτz.prodMk measurable_fst)
  have hAtPost : Measurable
      (fun z : Ω × ℝ => X.X (τ z.1 + Real.toNNReal z.2) z.1) :=
    hX.comp ((hτz.add hu).prodMk measurable_fst)
  have hPrefix : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) := by
    fun_prop
  have hPost : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))) := by
    fun_prop
  have hHPost : Measurable (fun z : Ω × ℝ =>
      H (Real.toNNReal z.2) (fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) :=
    hH.comp (hu.prodMk (hY.comp measurable_fst))
  exact ((hW.comp measurable_fst).mul hPrefix).mul (hPost.mul hHPost)
