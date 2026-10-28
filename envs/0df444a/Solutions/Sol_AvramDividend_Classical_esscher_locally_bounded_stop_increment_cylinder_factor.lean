-- Prove2me | solution 1 for AvramDividend.Classical.esscher_locally_bounded_stop_increment_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:41:06.654965+00:00
-- url     : https://prove2.me/submissions/00c24491-c02b-4ae2-bd40-755aac1b0dfa

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A finite-terminal Esscher stopped-increment law for an unbounded stop,
localised to any stopped-history event supported before the terminal cap. -/
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
  let σ : Ω → ℝ≥0 := fun ω => min (τ ω) H
  have hσstop : IsStoppingTime 𝓕
      (fun ω => (σ ω : WithTop ℝ≥0)) := by
    simpa only [σ, WithTop.coe_min] using (hstop.min_const H)
  have hσbound : ∀ ω, σ ω ≤ H := by
    intro ω
    exact min_le_right _ _
  have hA_H : MeasurableSet[𝓕 H] A := by
    have he : A ∩ {ω : Ω | τ ω ≤ H} = A :=
      Set.inter_eq_left.mpr hSupport
    simpa only [he] using hA H
  have hσHist : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | σ ω ≤ s}) := by
    intro s
    by_cases hs : H ≤ s
    · have he : {ω : Ω | σ ω ≤ s} = Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans (min_le_right _ _) hs
      simpa only [he, Set.inter_univ] using
        (𝓕.mono hs _ hA_H)
    · have hlt : s < H := lt_of_not_ge hs
      have he : {ω : Ω | σ ω ≤ s} = {ω : Ω | τ ω ≤ s} := by
        ext ω
        simp only [Set.mem_setOf_eq, σ, min_le_iff]
        constructor
        · intro hh
          exact hh.resolve_right (not_le.mpr hlt)
        · exact Or.inl
      simpa only [he] using hA s
  have hcyl := esscher_bounded_stop_future_increment_cylinder_factor
    X θ hθ σ hσstop H hσbound u T hT A hσHist B hB
  have hset :
      (A ∩ {ω : Ω |
        X.X (σ ω + u) ω - X.X (σ ω) ω ∈ B}) =
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) := by
    ext ω
    by_cases hw : ω ∈ A
    · have he : σ ω = τ ω := min_eq_left (hSupport hw)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hw, true_and, he]
    · simp only [Set.mem_inter_iff, hw, false_and]
  rw [hset] at hcyl
  exact hcyl
