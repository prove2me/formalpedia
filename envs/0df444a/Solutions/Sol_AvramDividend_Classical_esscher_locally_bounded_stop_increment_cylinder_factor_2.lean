-- Prove2me | solution 2 for AvramDividend.Classical.esscher_locally_bounded_stop_increment_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:41:22.085979+00:00
-- url     : https://prove2.me/submissions/2876ad1f-b049-4887-9572-72f65e89d8a4

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hSupport : A ⊆ {ω : Ω | τ ω ≤ H})
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  have hstop' : IsStoppingTime 𝓕 (fun ω => ((min (τ ω) H : ℝ≥0) : WithTop ℝ≥0)) := by
    have := hstop.min_const H
    convert this using 2 with ω
    exact WithTop.coe_min _ _
  have heq : ∀ ω ∈ A, min (τ ω) H = τ ω := fun ω hω => min_eq_left (hSupport hω)
  have hA' : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] (A ∩ {ω : Ω | min (τ ω) H ≤ s}) := by
    intro s
    have : A ∩ {ω : Ω | min (τ ω) H ≤ s} = A ∩ {ω : Ω | τ ω ≤ s} := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have h2' : min (τ ω) H ≤ s := h2
        rw [heq ω h1] at h2'; exact h2'
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show min (τ ω) H ≤ s
        rw [heq ω h1]; exact h2
    rw [this]; exact hA s
  have h := esscher_bounded_stop_future_increment_cylinder_factor X θ hθ (fun ω => min (τ ω) H)
    hstop' H (fun ω => min_le_right _ _) u T hT A hA' B hB
  have hs : A ∩ {ω : Ω | X.X (min (τ ω) H + u) ω - X.X (min (τ ω) H) ω ∈ B} =
      A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} := by
    ext ω
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [mem_setOf_eq, heq ω h1] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [mem_setOf_eq, heq ω h1] using h2⟩
  rw [← hs]
  exact h
