-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:42:51.226616+00:00
-- url     : https://prove2.me/submissions/5be2a4ab-b882-4f83-8692-18d4735715ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_source_condExp_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) P ∧
    (P[(fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (1 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  let V : Ω → ℝ := fun ω => Real.exp
    (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))
  let K : ℝ := Real.exp (-(h : ℝ) * X.ψ θ)
  let N : Ω → ℝ := fun ω => K * V ω
  have hSource :=
    avram_wave6_03_original_rightCont_stopped_source_condExp_laplace
      X τ hτ T hbounded h θ hθ
  change Integrable V P ∧
    (P[V | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => Real.exp ((h : ℝ) * X.ψ θ))) at hSource
  have hNI : Integrable N P := hSource.1.const_mul K
  have hPull : P[N | hτstop.measurableSpace] =ᵐ[P]
      (fun ω => K * (P[V | hτstop.measurableSpace]) ω) :=
    condExp_mul_of_stronglyMeasurable_left
      measurable_const.stronglyMeasurable hNI hSource.1
  have hNorm : P[N | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [hPull, hSource.2] with ω hp hq
    calc
      (P[N | hτstop.measurableSpace]) ω =
          K * (P[V | hτstop.measurableSpace]) ω := hp
      _ = 1 := by
        rw [hq]
        change Real.exp (-(h : ℝ) * X.ψ θ) *
          Real.exp ((h : ℝ) * X.ψ θ) = 1
        rw [← Real.exp_add]
        ring_nf
        simp
  have hEq : N = (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) := by
    funext ω
    change Real.exp (-(h : ℝ) * X.ψ θ) *
        Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) =
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ)
    rw [← Real.exp_add]
    congr 1
    ring
  change Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) P ∧
    (P[(fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) |
      hτstop.measurableSpace] =ᵐ[P] (fun _ => (1 : ℝ)))
  rw [← hEq]
  exact ⟨hNI, hNorm⟩
