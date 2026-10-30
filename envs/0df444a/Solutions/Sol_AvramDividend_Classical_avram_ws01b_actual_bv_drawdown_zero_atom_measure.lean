-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_bv_drawdown_zero_atom_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:38:50.971478+00:00
-- url     : https://prove2.me/submissions/20d03f92-7aff-4338-a428-710572369ba2

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_bv_drawdown_zero_atom
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The true original exponential-clock BV drawdown has a nonzero
zero-atom in the actual extended nonnegative pushforward measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hstanding : X.Standing) (hBV : X.BoundedVariation)
    (R φ : ℝ) (hR : 0 < R) (hφ : 0 < φ)
    (hroot : X.ψ φ = R) :
    ((P.prod (expMeasure R)).map
      (fun z : Ω × ℝ =>
        runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1))
      ({0} : Set ℝ) =
    ENNReal.ofReal (R / (φ * X.drift)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure R) :=
    isProbabilityMeasure_expMeasure hR
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure R)
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  have hD : Measurable D :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hMeas : MeasurableSet {z : Ω × ℝ | D z = 0} :=
    (measurableSet_singleton (0 : ℝ)).preimage hD
  have hIntegral :
      (∫ z : Ω × ℝ, if D z = 0 then (1 : ℝ) else 0 ∂μ) =
      μ.real {z : Ω × ℝ | D z = 0} := by
    simpa [Set.indicator, Pi.one_apply] using
      (integral_indicator_one hMeas)
  have hMass : μ.real {z : Ω × ℝ | D z = 0} =
      R / (φ * X.drift) := by
    rw [← hIntegral]
    simpa only [μ, D] using
      (avram_ws01b_actual_bv_drawdown_zero_atom
        X hstanding hBV R φ hR hφ hroot)
  have hFinite : μ {z : Ω × ℝ | D z = 0} ≠ ∞ :=
    ne_of_lt (measure_lt_top μ _)
  change (μ.map D) ({0} : Set ℝ) =
    ENNReal.ofReal (R / (φ * X.drift))
  rw [Measure.map_apply hD (measurableSet_singleton (0 : ℝ))]
  change μ {z : Ω × ℝ | D z = 0} =
    ENNReal.ofReal (R / (φ * X.drift))
  rw [← hMass]
  exact (ENNReal.ofReal_toReal hFinite).symm
