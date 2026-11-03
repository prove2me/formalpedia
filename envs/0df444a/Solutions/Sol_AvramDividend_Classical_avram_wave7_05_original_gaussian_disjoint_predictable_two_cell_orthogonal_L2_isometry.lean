-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_gaussian_disjoint_predictable_two_cell_orthogonal_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:48:59.436402+00:00
-- url     : https://prove2.me/submissions/fed86bdc-8f3f-4cbe-a161-4b60d0a926e9

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
    Integrable (fun ω => (A ω + B ω) ^ 2) P ∧
      (∫ ω, (A ω + B ω) ^ 2 ∂P) =
        (∫ ω, (A ω) ^ 2 ∂P) +
          (∫ ω, (B ω) ^ 2 ∂P) := by
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
  have hA2 : Integrable (fun ω => (A ω) ^ 2) P := by
    have hAeq : (A * A) = (fun ω => (A ω) ^ 2) := by
      funext ω
      simp only [Pi.mul_apply, pow_two]
    rw [← hAeq]
    exact hM1.integrable_mul hM1
  have hB2 : Integrable (fun ω => (B ω) ^ 2) P := by
    have hBeq : (B * B) = (fun ω => (B ω) ^ 2) := by
      funext ω
      simp only [Pi.mul_apply, pow_two]
    rw [← hBeq]
    exact hM2.integrable_mul hM2
  have hTwo : Integrable (fun ω => (2 : ℝ) * (A ω * B ω)) P :=
    hCrossI.const_mul 2
  have hExpand :
      (fun ω => (A ω + B ω) ^ 2) =
      (fun ω => (A ω) ^ 2 + (B ω) ^ 2 +
        (2 : ℝ) * (A ω * B ω)) := by
    funext ω
    ring
  have hTotal : Integrable (fun ω => (A ω + B ω) ^ 2) P := by
    rw [hExpand]
    exact (hA2.add hB2).add hTwo
  have hIntegralEq :
      (∫ ω, (P[A * B | 𝓕.rightCont u]) ω ∂P) =
        ∫ ω, A ω * B ω ∂P :=
    integral_condExp (𝓕.rightCont.le u)
  have hCrossZero : (∫ ω, A ω * B ω ∂P) = 0 := by
    calc
      (∫ ω, A ω * B ω ∂P) =
          ∫ ω, (P[A * B | 𝓕.rightCont u]) ω ∂P :=
        hIntegralEq.symm
      _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hCE
      _ = 0 := by simp
  change Integrable (fun ω => (A ω + B ω) ^ 2) P ∧
    (∫ ω, (A ω + B ω) ^ 2 ∂P) =
      (∫ ω, (A ω) ^ 2 ∂P) + (∫ ω, (B ω) ^ 2 ∂P)
  refine ⟨hTotal, ?_⟩
  calc
    (∫ ω, (A ω + B ω) ^ 2 ∂P) =
        ∫ ω, (A ω) ^ 2 + (B ω) ^ 2 +
          (2 : ℝ) * (A ω * B ω) ∂P := by rw [hExpand]
    _ = (∫ ω, (A ω) ^ 2 ∂P) +
        (∫ ω, (B ω) ^ 2 ∂P) +
          (2 : ℝ) * (∫ ω, A ω * B ω ∂P) := by
      have hOuter :
          (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 +
            (2 : ℝ) * (A ω * B ω) ∂P) =
          (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) +
            (∫ ω, (2 : ℝ) * (A ω * B ω) ∂P) := by
        simpa only [Pi.add_apply] using
          (integral_add (hA2.add hB2) hTwo)
      have hInner :
          (∫ ω, (A ω) ^ 2 + (B ω) ^ 2 ∂P) =
          (∫ ω, (A ω) ^ 2 ∂P) + (∫ ω, (B ω) ^ 2 ∂P) := by
        simpa only [Pi.add_apply] using (integral_add hA2 hB2)
      rw [hOuter, hInner, integral_const_mul]
    _ = (∫ ω, (A ω) ^ 2 ∂P) +
        (∫ ω, (B ω) ^ 2 ∂P) := by rw [hCrossZero]; ring
