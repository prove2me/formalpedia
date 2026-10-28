-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_random_terminal_esscher_clock_window_increment_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:48:29.855438+00:00
-- url     : https://prove2.me/submissions/a40100fc-59d3-48c4-9c7b-2d23cabb1526

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual random-terminal Esscher likelihood factors a bounded-stop
future-increment cylinder over a clock window lying past its adapted horizon. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hEvent : MeasurableSet
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}))
    (hEventAdapted : MeasurableSet[𝓕 (H + 1 + u)]
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}))
    {ν : Measure ℝ} [SFinite ν]
    (C : Set ℝ) (hC : MeasurableSet C)
    (hClockLow : ∀ t ∈ C, H + 1 + u ≤ Real.toNNReal t)
    (hClockHigh : ∀ t ∈ C, Real.toNNReal t ≤ T)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ))))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * ν C := by
  haveI := X.isProbability
  set Ev := A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} with hEv
  have hE : MeasurableSet (Ev ×ˢ C) := hEvent.prod hC
  have hSlice : ∀ t : ℝ, @MeasurableSet Ω (𝓕 (min t.toNNReal T)) {ω : Ω | (ω, t) ∈ Ev ×ˢ C} := by
    intro t
    by_cases ht : t ∈ C
    · have hle : H + 1 + u ≤ min t.toNNReal T := le_min (hClockLow t ht) hT
      have : {ω : Ω | (ω, t) ∈ Ev ×ˢ C} = Ev := by
        ext ω; simp [Set.mem_prod, ht]
      rw [this]
      exact 𝓕.mono hle _ hEventAdapted
    · have : {ω : Ω | (ω, t) ∈ Ev ×ˢ C} = ∅ := by
        ext ω; simp [Set.mem_prod, ht]
      rw [this]; exact @MeasurableSet.empty Ω (𝓕 (min t.toNNReal T))
  have hSupport : ∀ (ω : Ω) (t : ℝ), (ω, t) ∈ Ev ×ˢ C → t.toNNReal ≤ T :=
    fun ω t h => hClockHigh t h.2
  rw [esscher_clock_supported_stopped_event_laws_agree X θ hθ T (Ev ×ˢ C) hE hSlice hSupport hJoint,
    Measure.prod_prod,
    esscher_bounded_stop_future_increment_cylinder_factor X θ hθ τ hstop H hbound u T hT A hA B hB]
