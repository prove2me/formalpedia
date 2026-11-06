-- Prove2me | solution 1 for CondRiskMap.Repr.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:12:41.151466+00:00
-- url     : https://prove2.me/submissions/b3f56a41-4706-4847-8173-27ae1d0ca8b3

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting
import Theorems.Thm_CondRiskMap_Repr_dom_conj_subset_probGiven

open CondRiskMap.Repr MeasureTheory

namespace CRMProp3Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma pair_indicator (μ : SignedMeasure Ω) {B : Set Ω} (hB : MeasurableSet B) :
    pair μ (B.indicator 1) = μ B := by
  unfold pair
  rw [integral_indicator_one hB, integral_indicator_one hB]
  conv_rhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hB, Measure.toSignedMeasure_apply_measurable hB]

lemma nonneg_apply {v : SignedMeasure Ω} (hv : 0 ≤ v) {s : Set Ω} (hs : MeasurableSet s) :
    0 ≤ v s := by
  have := (VectorMeasure.le_iff.mp hv) s hs
  simpa using this

lemma mono_of_nonneg {v : SignedMeasure Ω} (hv : 0 ≤ v) {s t : Set Ω} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) : v s ≤ v t := by
  rw [← VectorMeasure.of_add_of_sdiff hs ht hst]
  linarith [nonneg_apply hv (ht.diff hs)]

end CRMProp3Aux

open CRMProp3Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) (hI : HasIndicators S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (κ : Ω → 𝒴) (hκ : IsSelection S ρ κ) (ν : 𝒴) (hν : ν ∈ Prob S)
    (hfix : IsFixedPoint S κ ν) :
    IsCondProb S ν κ := by
  have hP : ∀ ω, κ ω ∈ ProbGiven S ω := fun ω =>
    dom_conj_subset_probGiven S hC hC' ρ hρ hlsc ω (hκ.1 ω)
  refine ⟨?_, ?_⟩
  · intro A hA
    obtain ⟨X, hX⟩ := hI A hA
    have h := hκ.2 X
    have : (fun ω => pair (S.toMeasure (κ ω)) (S.toFun X)) =
        fun ω => S.toMeasure (κ ω) A := by
      funext ω; rw [hX, pair_indicator _ hA]
    rw [this] at h
    exact h
  · intro A B hA hB
    have hB2 : MeasurableSet B := S.F₁_le B hB
    have hAB : MeasurableSet (A ∩ B) := hA.inter hB2
    have hpt : (B.indicator fun ω => S.toMeasure (κ ω) A) =
        fun ω => S.toMeasure (κ ω) (A ∩ B) := by
      funext ω
      have hnn := (hP ω).1.1
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]
        have hsplit := VectorMeasure.of_add_of_sdiff (v := S.toMeasure (κ ω)) hAB hA
          Set.inter_subset_left
        have hsub : A \ (A ∩ B) ⊆ Bᶜ := by
          intro x hx; exact fun hxB => hx.2 ⟨hx.1, hxB⟩
        have hc := (hP ω).2 Bᶜ hB.compl
        rw [Set.indicator_of_notMem (by simpa using hω)] at hc
        have h1 := mono_of_nonneg hnn (hA.diff hAB) hB2.compl hsub
        have h2 := nonneg_apply hnn (hA.diff hAB)
        linarith
      · rw [Set.indicator_of_notMem hω]
        have hc := (hP ω).2 B hB
        rw [Set.indicator_of_notMem hω] at hc
        have h1 := mono_of_nonneg hnn hAB hB2 Set.inter_subset_right
        have h2 := nonneg_apply hnn hAB
        linarith
    rw [hpt]
    exact hfix (A ∩ B) hAB
