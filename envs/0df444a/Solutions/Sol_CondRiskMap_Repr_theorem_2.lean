-- Prove2me | solution 1 for CondRiskMap.Repr.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:07:45.49437+00:00
-- url     : https://prove2.me/submissions/5836cba6-c92b-43e3-b69a-0de6745434ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting
import Theorems.Thm_CondRiskMap_Repr_lemma_1
import Theorems.Thm_CondRiskMap_Repr_exists_fixedPoint_of_K
import Theorems.Thm_CondRiskMap_Repr_proposition_3
import Theorems.Thm_CondRiskMap_Repr_dom_conj_subset_probGiven

open CondRiskMap.Repr

theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴] [Nonempty Ω]
    [TopologicalSpace.SeparableSpace 𝒳]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) (hI : HasIndicators S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (hK : CondK S ρ) :
    ∃ (ν : ℕ → 𝒴) (κ : ℕ → Ω → 𝒴),
      (∀ i, ν i ∈ Prob S) ∧ (∀ i ω, κ i ω ∈ Prob S) ∧ (∀ i, IsWeakStarMeasurable S (κ i)) ∧
      (∀ i, IsCondProb S (ν i) (κ i)) ∧
      ∀ X ω, IsLUB (Set.range fun i => pair (S.toMeasure (κ i ω)) (S.toFun X)) (ρω S ρ ω X) := by
  obtain ⟨κ, hsel, hlub⟩ := lemma_1 S hC hC' ρ hρ hph hlsc
  have hfp : ∀ i, ∃ ν ∈ Prob S, IsFixedPoint S (κ i) ν := fun i =>
    exists_fixedPoint_of_K S hC hC' ρ hρ hph hlsc hK (κ i) (hsel i)
  choose ν hνP hνfix using hfp
  refine ⟨ν, κ, hνP, ?_, fun i => (hsel i).2, ?_, hlub⟩
  · intro i ω
    exact (dom_conj_subset_probGiven S hC hC' ρ hρ hlsc ω ((hsel i).1 ω)).1
  · intro i
    exact proposition_3 S hC hC' hI ρ hρ hph hlsc (κ i) (hsel i) (ν i) (hνP i) (hνfix i)
