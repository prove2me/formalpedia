-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_original_wh_product_killed_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:07:48.02829+00:00
-- url     : https://prove2.me/submissions/ef3a242f-fb1e-4dd9-b9ae-bfabe98a0133

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Actual original P × Exp(r) Wiener–Hopf independence factors a
closed lower-survival reward, preserving drawdown atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (x : ℝ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z : Ω × ℝ,
      (if runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1 ≤ x
       then g (x + runningSup X z.2.toNNReal z.1 -
          (runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1))
       else (0 : ℝ≥0∞))
      ∂(P.prod (expMeasure r))) =
    (∫⁻ a : ℝ × ℝ,
      if a.2 ≤ x then g (x + a.1 - a.2)
      else (0 : ℝ≥0∞)
      ∂((P.prod (expMeasure r)).map
          (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1)).prod
        ((P.prod (expMeasure r)).map
          (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1 -
              X.X z.2.toNNReal z.1))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let S : Ω × ℝ → ℝ := fun z => runningSup X z.2.toNNReal z.1
  let D : Ω × ℝ → ℝ := fun z => S z - X.X z.2.toNNReal z.1
  have hi : IndepFun S D μ := by
    simpa [S, D, μ] using
      (avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun X r hr)
  have hS : Measurable S :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  let f : ℝ × ℝ → ℝ≥0∞ := fun a =>
    if a.2 ≤ x then g (x + a.1 - a.2) else 0
  have hf : Measurable f := by
    have he : MeasurableSet {a : ℝ × ℝ | a.2 ≤ x} :=
      measurableSet_Iic.preimage measurable_snd
    exact Measurable.ite he
      (hg.comp ((measurable_const.add measurable_fst).sub measurable_snd))
      measurable_const
  have hMap := hi.map_prod_eq_prod_map_map hS.aemeasurable hD.aemeasurable
  change (∫⁻ z, f (S z, D z) ∂μ) =
    ∫⁻ a, f a ∂((μ.map S).prod (μ.map D))
  rw [← hMap, lintegral_map hf (hS.prodMk hD)]
