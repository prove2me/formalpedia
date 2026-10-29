-- Prove2me | solution 1 for AvramDividend.Classical.esscher_clock_supported_prefix_observable_lintegral_laws_agree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:06:56.489667+00:00
-- url     : https://prove2.me/submissions/37f972bd-48b7-4ef3-a0f0-38b4a8b80b17

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_prefix_observable_map_laws_agree
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (E : Set (Ω × ℝ)) (hE : MeasurableSet E)
    (hSlice : ∀ t : ℝ,
      @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | (ω, t) ∈ E})
    (hSupport : ∀ (ω : Ω) (t : ℝ),
      (ω, t) ∈ E → t.toNNReal ≤ T)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ))))
    {β : Type*} [MeasurableSpace β]
    (Y : (Ω × ℝ) → β) (hY : Measurable Y)
    (hYslice : ∀ (B : Set β), MeasurableSet B →
      ∀ t : ℝ, @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | Y (ω, t) ∈ B})
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in E, g (Y z) ∂
      ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))) =
    (∫⁻ z in E, g (Y z) ∂
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν)) := by
  let μReal : Measure (Ω × ℝ) :=
    (P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))
  let μTerm : Measure (Ω × ℝ) :=
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν
  have hm : Measure.map Y (μReal.restrict E) =
      Measure.map Y (μTerm.restrict E) :=
    esscher_clock_supported_prefix_observable_map_laws_agree
      X θ hθ T E hE hSlice hSupport hJoint Y hY hYslice
  change (∫⁻ z in E, g (Y z) ∂μReal) =
    (∫⁻ z in E, g (Y z) ∂μTerm)
  calc
    (∫⁻ z in E, g (Y z) ∂μReal) =
      ∫⁻ y, g y ∂Measure.map Y (μReal.restrict E) :=
        (lintegral_map hg hY).symm
    _ = ∫⁻ y, g y ∂Measure.map Y (μTerm.restrict E) := by
      rw [hm]
    _ = (∫⁻ z in E, g (Y z) ∂μTerm) :=
      lintegral_map hg hY
