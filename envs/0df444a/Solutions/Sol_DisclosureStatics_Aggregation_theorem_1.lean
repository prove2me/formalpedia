-- Prove2me | solution 1 for DisclosureStatics.Aggregation.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:08:43.266957+00:00
-- url     : https://prove2.me/submissions/6d94adfd-a064-4d85-a824-88b1dc7d7865
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model
import Theorems.Thm_DisclosureStatics_Aggregation_proposition_1
import Theorems.Thm_DisclosureStatics_Aggregation_proposition_2

open DisclosureStatics.Aggregation

theorem solution {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (hrB : rE M {M.s₁} ≤ rE M B) (hr1 : 1 ≤ rE M {M.s₁})
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct) :
    Loss M c < Loss M ct ∧ Loss M c < Loss M cs ∧ Loss M cs < Loss M ct := by
  have h1 := (proposition_1 M hM γ hγ φ hφ π hπ 𝒮 B hagg.1 hhet c cs hc hcs).2
  have h2 := proposition_2 M hM γ hγ φ hφ π ρ hπ 𝒮 B hagg hhet hrB hr1 c cs ct hc hcs hct
  refine ⟨?_, by linarith, h2⟩
  linarith
