-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian12_original_zero_jump_stopped_gaussian_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:38:29.40549+00:00
-- url     : https://prove2.me/submissions/b1cf1069-d014-4deb-ace4-1fad6b6d1dab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_variable_stops_predictable_taylor_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (G i))
    (hH : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (H i))
    (M : ι → Ω → ℝ)
    (hM : M = (fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    ∀ i (hi : i ∈ S),
      Integrable (F i) P ∧
        P[F i |
          (isStoppingTime_withTop_of_le_events (τ i)
            (hτ i hi)).measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  subst M
  have hSourceDecomp :
      ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        X.X u ω = (u : ℝ) * X.c +
          (X.X u ω - (u : ℝ) * X.c) +
          (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) u ω + (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) u ω := by
    filter_upwards [] with ω
    intro u
    ring
  have hResult :=
    AvramDividend.Classical.avram_p4_a_gaussian_ae_variable_stops_predictable_taylor_condExp_zero
      X X hν rfl (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ))
      hSourceDecomp S τ hτ B hbounded h G H hG hH
      (by
        intro i hi
        simpa only [sub_zero] using hGI i hi)
      hHI
      (by
        intro i hi
        simpa only [sub_zero] using hH2I i hi)
  simpa only [sub_zero] using hResult
