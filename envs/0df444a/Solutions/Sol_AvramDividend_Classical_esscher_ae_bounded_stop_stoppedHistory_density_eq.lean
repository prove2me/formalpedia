-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_density_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:39:01.284965+00:00
-- url     : https://prove2.me/submissions/7bf83f77-6931-47d4-92c3-41918727db24

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by
  set τ' : Ω → ℝ≥0 := fun ω => min (τ ω) H with hτ'
  have hstop' : IsStoppingTime 𝓕 (fun ω => (τ' ω : WithTop ℝ≥0)) := by
    have := hstop.min_const H
    simpa only [hτ', WithTop.coe_min] using this
  have hbound' : ∀ ω, τ' ω ≤ H := fun ω => min_le_right _ _
  have hττ' : ∀ᵐ ω ∂P, τ' ω = τ ω := by
    filter_upwards [haeBound] with ω hω
    exact min_eq_left hω
  set A' : Set Ω := A ∩ {ω | τ ω ≤ H} with hA'
  have hA's : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] (A' ∩ {ω : Ω | τ' ω ≤ s}) := by
    intro s
    have : A' ∩ {ω : Ω | τ' ω ≤ s} = A ∩ {ω : Ω | τ ω ≤ min s H} := by
      ext ω
      simp only [hA', hτ', Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff, min_le_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
        · exact ⟨h1, h3, h2⟩
        · exact ⟨h1, le_trans h2 h3, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h3⟩, Or.inl h2⟩
    rw [this]
    exact 𝓕.mono (min_le_left s H) _ (hA (min s H))
  have h := AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_density_eq X θ hθ τ' hstop' H
    hbound' T hT A' hA's
  have hdens : (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ' ω) ω - (τ' ω : ℝ) * X.ψ θ)))) =
      (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by
    apply withDensity_congr_ae
    filter_upwards [hττ'] with ω hω
    rw [hω]
  rw [hdens] at h
  have e : ∀ (μ : Measure Ω), μ ≪ P → μ A' = μ A := by
    intro μ hμ
    apply measure_congr
    filter_upwards [hμ.ae_le haeBound] with ω hω
    apply propext
    show ω ∈ (_ : Set Ω) ↔ ω ∈ (_ : Set Ω)
    simp only [hA', Set.mem_inter_iff, Set.mem_setOf_eq, hω, and_true]
  rw [← e _ (withDensity_absolutelyContinuous _ _), h, e _ (withDensity_absolutelyContinuous _ _)]
