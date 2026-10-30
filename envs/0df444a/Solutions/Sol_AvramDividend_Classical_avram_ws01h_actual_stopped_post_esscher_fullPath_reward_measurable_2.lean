-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:00:07.155324+00:00
-- url     : https://prove2.me/submissions/8dcc457f-e87c-46f3-829c-1d94662c76bb

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable

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
  have hJ := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have h2 := (AvramDividend.Classical.avram_ws01e_b_joint_wholePath_stopped_reward_measurable
    X τ hτ H hH (fun _ => 0) measurable_const).1
  have hA : Measurable (fun z : Ω × ℝ => X.X (τ z.1 + Real.toNNReal z.2) z.1) :=
    hJ.comp (((hτ.comp measurable_fst).add (measurable_real_toNNReal.comp measurable_snd)).prodMk
      measurable_fst)
  have hB : Measurable (fun z : Ω × ℝ => X.X (τ z.1) z.1) :=
    hJ.comp ((hτ.comp measurable_fst).prodMk measurable_fst)
  refine Measurable.mul ?_ h2
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  exact (measurable_const.mul (hA.sub hB)).sub
    ((measurable_coe_nnreal_real.comp (measurable_real_toNNReal.comp measurable_snd)).mul measurable_const)
