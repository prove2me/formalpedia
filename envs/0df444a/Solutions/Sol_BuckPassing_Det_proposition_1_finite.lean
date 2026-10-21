-- Prove2me | solution 1 for BuckPassing.Det.proposition_1_finite
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:18.08001+00:00
-- url     : https://prove2.me/submissions/d00e08ab-f8d5-4258-8f8d-32e0bc85117a

import Mathlib
import Definitions.Def_BuckPassing_Det_CostGame
set_option autoImplicit false
open BuckPassing.Det

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (c : ι → (∀ i, X i) → ℝ) (Ψ : (∀ i, X i) → ℝ)
    (hpot : IsGenOrdPotential c Ψ) :
    ∃ s : ∀ i, X i, IsNash c s := by
  obtain ⟨s, hs⟩ := Finite.exists_min Ψ
  refine ⟨s, fun i x hlt => ?_⟩
  exact absurd (hpot s i x hlt) (not_lt.mpr (hs _))
