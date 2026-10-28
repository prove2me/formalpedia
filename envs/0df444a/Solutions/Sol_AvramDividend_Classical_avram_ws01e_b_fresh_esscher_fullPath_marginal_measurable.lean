-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fresh_esscher_fullPath_marginal_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:43:12.267925+00:00
-- url     : https://prove2.me/submissions/6c5b6ee1-6297-46fa-a4ee-5c6c2bc200f0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      H z.1 z.2)) :
    Measurable (fun r : ℝ =>
      (∫⁻ ω : Ω,
        ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal r) ω -
            (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r)
          (fun s : ℝ≥0 => X.X s ω) ∂P)) := by
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hZ : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) :=
    levy_wholePath_measurable X
  have ht : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) := by
    fun_prop
  have hEval : Measurable
      (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) :=
    hX.comp (ht.prodMk measurable_fst)
  have hW : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))) := by
    fun_prop
  have hF : Measurable (fun z : Ω × ℝ =>
      H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X s z.1)) :=
    hH.comp (ht.prodMk (hZ.comp measurable_fst))
  exact Measurable.lintegral_prod_left (hW.mul hF)
