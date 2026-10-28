-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_joint_wholePath_stopped_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:42:58.834778+00:00
-- url     : https://prove2.me/submissions/11751927-6222-4ce5-b2bf-0fd2bafdfc45

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

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
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2))
    (W : Ω → ℝ≥0∞) (hW : Measurable W) :
    Measurable (fun z : Ω × ℝ =>
      H (Real.toNNReal z.2)
        (fun s : ℝ≥0 =>
          X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) ∧
    Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 =>
          X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) := by
  have hY : Measurable (fun ω : Ω => fun s : ℝ≥0 =>
    X.X (τ ω + s) ω - X.X (τ ω) ω) :=
    avram_ws01e_b_randomAge_whole_shiftedPath_measurable X τ hτ
  have hT : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) := by
    fun_prop
  have hR : Measurable
      (fun z : Ω × ℝ => Real.toNNReal (z.2 - (τ z.1 : ℝ))) := by
    fun_prop
  constructor
  · exact hH.comp (hT.prodMk (hY.comp measurable_fst))
  · exact (hW.comp measurable_fst).mul
      (hH.comp (hR.prodMk (hY.comp measurable_fst)))
