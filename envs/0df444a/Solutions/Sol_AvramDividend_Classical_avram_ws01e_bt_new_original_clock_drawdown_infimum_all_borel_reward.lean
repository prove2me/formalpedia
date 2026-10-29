-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:30:49.445069+00:00
-- url     : https://prove2.me/submissions/c4961005-8b76-4f16-980d-6aba47ea8b4c

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Every Borel ENNReal reward of the genuine original-clock
terminal drawdown agrees with the corresponding centred infimum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : Ω × ℝ,
      f (runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1)
      ∂(P.prod (expMeasure p))) =
    (∫⁻ z : Ω × ℝ,
      f (X.X 0 z.1 +
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1})
      ∂(P.prod (expMeasure p))) := by
  classical
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  let I : Ω × ℝ → ℝ := fun z =>
    X.X 0 z.1 + -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hD : Measurable D := by simpa only [D] using hTri.snd
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hI : Measurable I := hX0.add (by
    simpa only [I] using hTri.fst.snd)
  have hLaw : μ.map D = μ.map I := by
    simpa only [μ, D, I] using
      (avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
        X p hp)
  change (∫⁻ z, f (D z) ∂μ) = (∫⁻ z, f (I z) ∂μ)
  calc
    (∫⁻ z, f (D z) ∂μ) =
        (∫⁻ x, f x ∂μ.map D) := (lintegral_map hf hD).symm
    _ = (∫⁻ x, f x ∂μ.map I) := by rw [hLaw]
    _ = (∫⁻ z, f (I z) ∂μ) := lintegral_map hf hI
