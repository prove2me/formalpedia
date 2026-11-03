-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_gaussian_disjoint_predictable_cross_expectation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:34:55.941576+00:00
-- url     : https://prove2.me/submissions/97266355-5f4c-4962-af1a-1c98af20d436

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (G H : Ω → ℝ)
    (hG : Measurable[𝓕.rightCont u] G)
    (hH : Measurable[𝓕.rightCont u] H)
    (hM1 : MemLp (fun ω =>
      G ω * (X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c)) 2 P)
    (hM2 : MemLp (fun ω =>
      H ω * (X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c)) 2 P) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    let A : Ω → ℝ := G * Y₁
    let B : Ω → ℝ := H * Y₂
    Integrable (A * B) P ∧ (∫ ω, A ω * B ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y₁ : Ω → ℝ := fun ω =>
    X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let Y₂ : Ω → ℝ := fun ω =>
    X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
  let A : Ω → ℝ := G * Y₁
  let B : Ω → ℝ := H * Y₂
  have hOrth :=
    avram_wave6_03_original_rightCont_gaussian_disjoint_predictable_L2_bilinear_cross_condExp_zero
      X hν s t u v hst htu huv G H hG hH hM1 hM2
  dsimp only at hOrth
  have hCrossI : Integrable (A * B) P := hOrth.1
  have hCE : P[A * B | 𝓕.rightCont u] =ᵐ[P] (fun _ => (0 : ℝ)) :=
    hOrth.2
  have hIntegralEq :
      (∫ ω, (P[A * B | 𝓕.rightCont u]) ω ∂P) =
        ∫ ω, A ω * B ω ∂P :=
    integral_condExp (𝓕.rightCont.le u)
  change Integrable (A * B) P ∧ (∫ ω, A ω * B ω ∂P) = 0
  refine ⟨hCrossI, ?_⟩
  calc
    (∫ ω, A ω * B ω ∂P) =
        ∫ ω, (P[A * B | 𝓕.rightCont u]) ω ∂P :=
      hIntegralEq.symm
    _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hCE
    _ = 0 := by simp
