-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:58:27.803994+00:00
-- url     : https://prove2.me/submissions/90b6a8d0-7759-4c37-b50e-96a05c1b4318

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
        H (Real.toNNReal z.2)
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) := by
  have hClock : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) :=
    measurable_real_toNNReal.comp measurable_snd
  have hStopped : Measurable (fun z : Ω × ℝ => τ z.1) :=
    hτ.comp measurable_fst
  have hAfter : Measurable (fun z : Ω × ℝ =>
      X.X (τ z.1 + Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp
      ((hStopped.add hClock).prodMk measurable_fst)
  have hBefore : Measurable (fun z : Ω × ℝ => X.X (τ z.1) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (hStopped.prodMk measurable_fst)
  have hRealClock : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2 : ℝ)) :=
    measurable_coe_nnreal_real.comp hClock
  have hDensity : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (hAfter.sub hBefore)).sub
          (hRealClock.mul measurable_const)))
  have hFresh : Measurable (fun z : Ω × ℝ =>
      H (Real.toNNReal z.2)
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) :=
    (avram_ws01e_b_joint_wholePath_stopped_reward_measurable
      X τ hτ H hH (fun _ => 1) measurable_const).1
  exact hDensity.mul hFresh
