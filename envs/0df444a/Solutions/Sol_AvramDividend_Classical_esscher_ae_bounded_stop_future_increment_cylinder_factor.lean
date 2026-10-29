-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ae_bounded_stop_future_increment_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:37:43.515989+00:00
-- url     : https://prove2.me/submissions/554ac1e8-810b-4dff-ba43-2ad69a057766

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
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
  set μT := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))) with hμT
  have haeμ : ∀ᵐ ω ∂μT, τ ω ≤ H := (withDensity_absolutelyContinuous _ _).ae_le haeBound
  set A' : Set Ω := A ∩ {ω | τ ω ≤ H} with hA'
  have hA's : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] (A' ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    have : A' ∩ {ω : Ω | τ ω ≤ s} = A ∩ {ω : Ω | τ ω ≤ min s H} := by
      ext ω; simp only [hA', Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff]; tauto
    rw [this]
    exact 𝓕.mono (min_le_left s H) _ (hA (min s H))
  have h := AvramDividend.Classical.esscher_locally_bounded_stop_increment_cylinder_factor X θ hθ τ hstop H
    u T hT A' hA's Set.inter_subset_right B hB
  have e1 : (A' ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} : Set Ω) =ᵐ[μT]
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} : Set Ω) := by
    filter_upwards [haeμ] with ω hω
    apply propext
    show ω ∈ (_ : Set Ω) ↔ ω ∈ (_ : Set Ω)
    simp only [hA', Set.mem_inter_iff, Set.mem_setOf_eq, hω, and_true]
  have e2 : (A' : Set Ω) =ᵐ[μT] (A : Set Ω) := by
    filter_upwards [haeμ] with ω hω
    apply propext
    show ω ∈ (_ : Set Ω) ↔ ω ∈ (_ : Set Ω)
    simp only [hA', Set.mem_inter_iff, Set.mem_setOf_eq, hω, and_true]
  rw [← measure_congr e1, ← measure_congr e2]
  exact h
