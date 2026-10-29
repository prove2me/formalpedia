-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_all_borel_nonnegative_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:53:57.352768+00:00
-- url     : https://prove2.me/submissions/09ed099e-deaa-4d70-9e2c-af775aef320b

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Arbitrary nonnegative measurable original-clock supremum and
terminal-drawdown rewards factor exactly under the true product law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    (∫⁻ z, f (S z) * g (D z) ∂(P.prod (expMeasure p))) =
      (∫⁻ z, f (S z) ∂(P.prod (expMeasure p))) *
      (∫⁻ z, g (D z) ∂(P.prod (expMeasure p))) := by
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let S : Ω × ℝ → ℝ :=
    fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ :=
    fun z => S z - X.X (Real.toNNReal z.2) z.1
  have hS : Measurable S :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hInd : IndepFun S D μ :=
    avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun X p hp
  have hTest : IndepFun (f ∘ S) (g ∘ D) μ := hInd.comp hf hg
  change (∫⁻ z, (f ∘ S) z * (g ∘ D) z ∂μ) =
    (∫⁻ z, (f ∘ S) z ∂μ) * (∫⁻ z, (g ∘ D) z ∂μ)
  exact ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hf.comp hS) (hg.comp hD) hTest
