-- Prove2me | solution 1 for BuckPassing.Det.proposition_1_compact
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:42.78058+00:00
-- url     : https://prove2.me/submissions/13e8a0d4-44d8-4e4a-8822-157e9f172577

import Mathlib
import Definitions.Def_BuckPassing_Det_CostGame
set_option autoImplicit false
open BuckPassing.Det

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    (c : ι → (∀ i, X i) → ℝ) (Ψ : (∀ i, X i) → ℝ)
    (hpot : IsGenOrdPotential c Ψ) (hlsc : LowerSemicontinuous Ψ) :
    ∃ s : ∀ i, X i, IsNash c s := by
  obtain ⟨s, -, hs⟩ := (hlsc.lowerSemicontinuousOn Set.univ).exists_isMinOn
    (Set.univ_nonempty) isCompact_univ
  refine ⟨s, fun i x hlt => ?_⟩
  exact absurd (hpot s i x hlt) (not_lt.mpr (hs (Set.mem_univ _)))
