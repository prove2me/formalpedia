-- Prove2me | solution 1 for AvramDividend.Classical.esscher_clock_supported_prefix_observable_map_laws_agree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:56:07.097977+00:00
-- url     : https://prove2.me/submissions/d2803bd2-28e0-47d8-9e35-87864ecc7995

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree
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
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (E : Set (Ω × ℝ))
    (hE : MeasurableSet E)
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
        {ω : Ω | Y (ω, t) ∈ B}) :
    Measure.map Y
      (((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ)))).restrict E) =
    Measure.map Y
      (((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν).restrict E) := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hY hB, Measure.map_apply hY hB]
  rw [Measure.restrict_apply (hY hB),
      Measure.restrict_apply (hY hB)]
  have hPre : MeasurableSet ((Y ⁻¹' B) ∩ E) :=
    (hY hB).inter hE
  have hFibre : ∀ t : ℝ,
      @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | (ω, t) ∈ (Y ⁻¹' B) ∩ E} := by
    intro t
    change @MeasurableSet Ω (𝓕 (min t.toNNReal T))
      ({ω : Ω | Y (ω, t) ∈ B} ∩
        {ω : Ω | (ω, t) ∈ E})
    exact (hYslice B hB t).inter (hSlice t)
  have hSup : ∀ (ω : Ω) (t : ℝ),
      (ω, t) ∈ (Y ⁻¹' B) ∩ E →
        t.toNNReal ≤ T := by
    intro ω t hz
    exact hSupport ω t hz.2
  exact esscher_clock_supported_stopped_event_laws_agree
    X θ hθ T ((Y ⁻¹' B) ∩ E) hPre hFibre hSup hJoint
