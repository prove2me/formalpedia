-- Prove2me | solution 1 for ConvexRiskFn.Dual.dual_cone
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:26:51.437425+00:00
-- url     : https://prove2.me/submissions/43158bc7-e966-4fba-b320-18f6ef0bf83b

import Definitions.Def_ConvexRiskFn_Dual_Setting
set_option autoImplicit false
open MeasureTheory ConvexRiskFn.Dual Set

private theorem pair_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : SignedMeasure Ω) (hμ : 0 ≤ μ) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) :
    0 ≤ pair μ X := by
  let ν := μ.toMeasureOfZeroLE univ MeasurableSet.univ
    ((VectorMeasure.le_restrict_univ_iff_le _ _).mpr hμ)
  let j : JordanDecomposition Ω := ⟨ν,0,Measure.MutuallySingular.zero_right⟩
  have hj : j.toSignedMeasure=μ := by
    simp only [JordanDecomposition.toSignedMeasure,j,Measure.toSignedMeasure_zero,sub_zero]
    exact μ.toMeasureOfZeroLE_toSignedMeasure _
  have he : μ.toJordanDecomposition=j := by
    rw [← hj,JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  unfold pair
  rw [he]
  change 0 ≤ (∫ ω, X ω ∂ν) - (∫ ω, X ω ∂(0:Measure Ω))
  simp only [integral_zero_measure,sub_zero]
  exact integral_nonneg hX

theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳]
    [Module ℝ 𝒳] [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳]
    [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S) :
    Ypos S = {μ | μ ∈ S.Y ∧ ∀ X ∈ Xpos S, 0 ≤ pair μ (S.toFun X)} := by
  ext μ
  constructor
  · rintro ⟨hY,hμ⟩
    refine ⟨hY,?_⟩
    intro X hX
    exact pair_nonnegative μ hμ _ hX
  · rintro ⟨hY,h⟩
    refine ⟨hY,?_⟩
    by_contra hn
    obtain ⟨X,hX,hneg⟩ := hC μ hY hn
    exact (not_lt_of_ge (h X hX)) hneg

#print axioms solution

open ConvexRiskFn.Dual Filter Topology
namespace ConvexRiskFn.Dual

/-- §2, p. 434: under condition (C), the cone `𝒴₊` of nonnegative measures is dual to the cone
`𝒳₊` of nonnegative functions: `𝒴₊ = {μ ∈ 𝒴 : ⟨μ, X⟩ ≥ 0 ∀ X ∈ 𝒳₊}`. -/
example {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S) :
    Ypos S = {μ | μ ∈ S.Y ∧ ∀ X ∈ Xpos S, 0 ≤ pair μ (S.toFun X)} := by
  exact solution S hC
end ConvexRiskFn.Dual

#print axioms solution
