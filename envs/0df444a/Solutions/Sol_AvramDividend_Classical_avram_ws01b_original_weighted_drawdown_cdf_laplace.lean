-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_original_weighted_drawdown_cdf_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:29:09.285327+00:00
-- url     : https://prove2.me/submissions/af244019-24bd-4a31-8f21-df0d0bd8d852

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Actual original Exp(r) drawdown's exponentially weighted lower
cumulative has the exact shifted Laplace transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r φ β : ℝ) (hr : 0 < r) (hφ : 0 < φ) (hβφ : φ < β) :
    let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
    let D : Ω × ℝ → ℝ :=
      fun z => runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
    let ρ : Measure ℝ := Measure.map D μ
    let ζ : Measure ℝ := ρ.withDensity
      (fun z => ENNReal.ofReal (Real.exp (-φ * z)))
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-(β - φ) * x)) * ζ (Iic x)) =
      ENNReal.ofReal (1 / (β - φ)) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ρ) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let D : Ω × ℝ → ℝ :=
    fun z => runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  let ρ : Measure ℝ := Measure.map D μ
  haveI : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map μ D
  let w : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-φ * z))
  let ζ : Measure ℝ := ρ.withDensity w
  haveI : SFinite ζ := inferInstance
  have hmD : Measurable D :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hNonneg : ∀ z : Ω × ℝ, 0 ≤ D z := by
    intro z
    exact sub_nonneg.mpr ((runningSup_monotone_and_path_le X z.1).2 z.2.toNNReal)
  have hEmpty : D ⁻¹' Iio (0 : ℝ) = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
    exact not_lt.mpr (hNonneg z)
  have hρsupp : ρ (Iio 0) = 0 := by
    change (Measure.map D μ) (Iio 0) = 0
    rw [Measure.map_apply hmD measurableSet_Iio, hEmpty]
    exact measure_empty
  have hζsupp : ζ (Iio 0) = 0 :=
    (withDensity_absolutelyContinuous ρ w) hρsupp
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hg : Measurable (fun z : ℝ =>
      ENNReal.ofReal (Real.exp (-(β - φ) * z))) := by fun_prop
  have hMoment :
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(β - φ) * z)) ∂ζ) =
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ρ) := by
    change (∫⁻ z : ℝ, ENNReal.ofReal
      (Real.exp (-(β - φ) * z)) ∂ρ.withDensity w) = _
    rw [lintegral_withDensity_eq_lintegral_mul ρ hw hg]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (Real.exp (-φ * z)) *
      ENNReal.ofReal (Real.exp (-(β - φ) * z)) = _
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫⁻ x : ℝ in Ioi 0,
    ENNReal.ofReal (Real.exp (-(β - φ) * x)) * ζ (Iic x)) =
    ENNReal.ofReal (1 / (β - φ)) *
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ρ)
  rw [← hMoment]
  exact positiveLaplace_cumulative_measure ζ (β - φ)
    (sub_pos.mpr hβφ) hζsupp
