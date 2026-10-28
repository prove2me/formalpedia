-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_finite_grid_full_clock_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:20:58.535931+00:00
-- url     : https://prove2.me/submissions/a3318987-5aa9-44c1-9b82-5750502d4cfe

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_variable_clock_tail_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
/-- Genuine Esscher random-clock law for the complete finite-grid
stopped-increment and variable-tail event, not just its cell sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      s + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
        z.2 ∈ C (τ z.1)} =
    ∑ s ∈ grid,
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * (expMeasure p) (C s) := by
  have hCells : ∀ s ∈ grid, MeasurableSet
      (((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) ×ˢ C s) := by
    intro s hs
    exact (𝓕.le (s + u) _ (hAdapted s hs)).prod (hC s hs)
  let F : ℝ≥0 → Set (Ω × ℝ) := fun s =>
    ((A ∩ {ω : Ω | τ ω = s}) ∩
      (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) ×ˢ C s
  have hUnion :
      {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
        z.2 ∈ C (τ z.1)} = ⋃ s ∈ grid, F s := by
    ext z
    simp only [F, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hA, hs, hB, hC⟩
      exact ⟨τ z.1, hs, ⟨⟨hA, rfl⟩, hB⟩, hC⟩
    · rintro ⟨s, hs, ⟨⟨hA, hτ⟩, hB⟩, hC⟩
      subst s
      exact ⟨hA, hs, hB, hC⟩
  have hDisj : (↑grid : Set ℝ≥0).PairwiseDisjoint F := by
    intro s hs t ht hst
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hzs : τ z.1 = s := hz.1.1.2
    have hzt : τ z.1 = t := hz'.1.1.2
    exact hst (hzs.symm.trans hzt)
  rw [hUnion, measure_biUnion_finset hDisj hCells]
  exact avram_ws01e_b_support_finite_grid_variable_clock_tail_factor
    X θ p hθ hp τ grid u A hHistory B hB
      hAdapted C hC hClockTail hJoint
