-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_history_future_increment_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:49:28.21265+00:00
-- url     : https://prove2.me/submissions/e9ce2889-15df-45d3-954b-7897697bbdad

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        (A ∩ {ω : Ω | τ ω = s}))
    (hAdapted : ∀ B : Set ℝ, MeasurableSet B → ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      s + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hY : Measurable (fun z : Ω × ℝ =>
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1))
    (hXu : Measurable (X.X u)) :
    let QP : Measure (Ω × ℝ) :=
      ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    let QU : Measure Ω :=
      P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let E : Set (Ω × ℝ) :=
      {z : Ω × ℝ | z.1 ∈ A ∧ τ z.1 ∈ grid ∧ z.2 ∈ C (τ z.1)}
    Measure.map (fun z : Ω × ℝ =>
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)
      (QP.restrict E) = QP E • Measure.map (X.X u) QU := by
  intro QP QU E
  ext B hB
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB),
      Measure.smul_apply, Measure.map_apply hXu hB, smul_eq_mul]
  have hFactor :=
    avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history
      X θ p hθ hp τ grid u A hHistory hBaseAdapted
      B hB (hAdapted B hB) C hC hClockTail hJoint
  calc
    QP ((fun z : Ω × ℝ =>
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1) ⁻¹' B ∩ E) =
      QP {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
        z.2 ∈ C (τ z.1)} := by
          congr 1
          ext z
          simp only [E, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_preimage]
          tauto
    _ = QU ((X.X u) ⁻¹' B) * QP E := hFactor
    _ = QP E * QU ((X.X u) ⁻¹' B) := mul_comm _ _
