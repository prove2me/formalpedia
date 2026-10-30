-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:53:16.178773+00:00
-- url     : https://prove2.me/submissions/f6d205c7-6453-4ea9-a9f5-4ad15925775a

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal r) ω -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  have hClock : Measurable (fun z : ℝ × Ω => Real.toNNReal z.1) :=
    measurable_real_toNNReal.comp measurable_fst
  have hState : Measurable (fun z : ℝ × Ω =>
      X.X (Real.toNNReal z.1) z.2) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (hClock.prodMk measurable_snd)
  have hRealClock : Measurable (fun z : ℝ × Ω =>
      (Real.toNNReal z.1 : ℝ)) :=
    hClock.coe_nnreal_real
  have hPath : Measurable (fun ω : Ω =>
      (fun t : ℝ≥0 => X.X t ω)) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (chat04_levy_joint_time_state_measurable X).comp
      (measurable_const.prodMk measurable_id)
  have hPair : Measurable (fun z : ℝ × Ω =>
      (Real.toNNReal z.1, fun t : ℝ≥0 => X.X t z.2)) :=
    hClock.prodMk (hPath.comp measurable_snd)
  have hDensity : Measurable (fun z : ℝ × Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.1) z.2 -
          (Real.toNNReal z.1 : ℝ) * X.ψ θ))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul hState).sub
          (hRealClock.mul measurable_const)))
  have hReward : Measurable (fun z : ℝ × Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.1) z.2 -
          (Real.toNNReal z.1 : ℝ) * X.ψ θ)) *
        H (Real.toNNReal z.1) (fun t : ℝ≥0 => X.X t z.2)) :=
    hDensity.mul (hH.comp hPair)
  exact hReward.lintegral_prod_right
