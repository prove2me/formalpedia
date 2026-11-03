-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_disjoint_cross_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:06:07.194572+00:00
-- url     : https://prove2.me/submissions/e7ab7b6b-a388-4ce0-9716-ecb8fced42c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero

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
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
    Integrable (Y₁ * Y₂) P ∧
      (∫ ω, Y₁ ω * Y₂ ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y₁ : Ω → ℝ := fun ω =>
    X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let Y₂ : Ω → ℝ := fun ω =>
    X.X v ω - X.X u ω - ((v - u) : ℝ) * X.c
  have hOrth :=
    avram_wave6_03_original_rightCont_gaussian_disjoint_increment_L2_condExp_zero
      X hν s t u v hst htu huv
  have hCrossI : Integrable (Y₁ * Y₂) P := hOrth.2.2.1
  have hCE : P[Y₁ * Y₂ | 𝓕.rightCont u] =ᵐ[P]
      (fun _ => (0 : ℝ)) := hOrth.2.2.2
  have hIntegralEq :
      (∫ ω, (P[Y₁ * Y₂ | 𝓕.rightCont u]) ω ∂P) =
        ∫ ω, Y₁ ω * Y₂ ω ∂P :=
    integral_condExp (𝓕.rightCont.le u)
  change Integrable (Y₁ * Y₂) P ∧
    (∫ ω, Y₁ ω * Y₂ ω ∂P) = 0
  refine ⟨hCrossI, ?_⟩
  calc
    (∫ ω, Y₁ ω * Y₂ ω ∂P) =
        ∫ ω, (P[Y₁ * Y₂ | 𝓕.rightCont u]) ω ∂P := hIntegralEq.symm
    _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hCE
    _ = 0 := by simp
