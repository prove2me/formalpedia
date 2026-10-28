-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_history_two_increment_joint_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:00:24.387028+00:00
-- url     : https://prove2.me/submissions/a4ad3208-84d9-40d1-a879-ba77420953c8

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_two_step_grid_survival_history_independence
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

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
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u v : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseMiddle : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u)) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseFinal : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 ((s + u) + v)) (A ∩ {ω : Ω | τ ω = s}))
    (hMiddle : ∀ (B₁ : Set ℝ), MeasurableSet B₁ → ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁))
    (hFinal : ∀ (B₁ B₂ : Set ℝ), MeasurableSet B₁ → MeasurableSet B₂ →
      ∀ s ∈ grid, @MeasurableSet Ω (𝓕 ((s + u) + v))
        (((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
          (fun ω : Ω => X.X ((s + u) + v) ω -
            X.X (s + u) ω) ⁻¹' B₂))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      (s + u) + v ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hY : Measurable (fun z : Ω × ℝ =>
      (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1,
       X.X ((τ z.1 + u) + v) z.1 - X.X (τ z.1 + u) z.1)))
    (hXu : Measurable (X.X u)) (hXv : Measurable (X.X v)) :
    let QP : Measure (Ω × ℝ) :=
      ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    let QU : Measure Ω :=
      P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let QV : Measure Ω :=
      P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)))
    let E : Set (Ω × ℝ) :=
      {z : Ω × ℝ | z.1 ∈ A ∧ τ z.1 ∈ grid ∧ z.2 ∈ C (τ z.1)}
    Measure.map (fun z : Ω × ℝ =>
      (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1,
       X.X ((τ z.1 + u) + v) z.1 - X.X (τ z.1 + u) z.1))
      (QP.restrict E) =
    QP E • ((Measure.map (X.X u) QU).prod (Measure.map (X.X v) QV)) := by
  intro QP QU QV E
  letI : IsProbabilityMeasure QP :=
    chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X θ p hθ hp hJoint
  letI : IsProbabilityMeasure QV :=
    chat04_esscher_weighted_finite_horizon_probability X v θ hθ
  letI : IsFiniteMeasure (QP.restrict E) := inferInstance
  letI : IsFiniteMeasure
      (Measure.map (fun z : Ω × ℝ =>
        (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1,
         X.X ((τ z.1 + u) + v) z.1 - X.X (τ z.1 + u) z.1))
        (QP.restrict E)) :=
    Measure.isFiniteMeasure_map _ _
  apply Measure.ext_prod
  intro B₁ B₂ hB₁ hB₂
  rw [Measure.map_apply hY (hB₁.prod hB₂),
      Measure.restrict_apply (hY (hB₁.prod hB₂)),
      Measure.smul_apply, Measure.prod_prod,
      Measure.map_apply hXu hB₁, Measure.map_apply hXv hB₂,
      smul_eq_mul]
  have hFactor :=
    avram_ws01e_b_support_two_step_grid_survival_history_independence
      X θ p hθ hp τ grid u v A hHistory hBaseMiddle hBaseFinal
      B₁ B₂ hB₁ hB₂ (hMiddle B₁ hB₁) (hFinal B₁ B₂ hB₁ hB₂)
      C hC hClockTail hJoint
  calc
    QP ((fun z : Ω × ℝ =>
      (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1,
       X.X ((τ z.1 + u) + v) z.1 - X.X (τ z.1 + u) z.1))
      ⁻¹' (B₁ ×ˢ B₂) ∩ E) =
      QP {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B₁ ∧
        X.X ((τ z.1 + u) + v) z.1 -
          X.X (τ z.1 + u) z.1 ∈ B₂ ∧
        z.2 ∈ C (τ z.1)} := by
          congr 1
          ext z
          simp only [E, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_preimage, Set.mem_prod]
          tauto
    _ = QU ((X.X u) ⁻¹' B₁) * QV ((X.X v) ⁻¹' B₂) *
      QP E := hFactor
    _ = QP E * (QU ((X.X u) ⁻¹' B₁) *
      QV ((X.X v) ⁻¹' B₂)) := by ac_rfl
