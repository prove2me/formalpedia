-- Prove2me | solution 1 for BuckPassing.Det.minimizer_isNash
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:16.813226+00:00
-- url     : https://prove2.me/submissions/a4fb75af-8a7f-4ec0-a079-608b23dc207a

import Mathlib
import Definitions.Def_BuckPassing_Det_CostGame
set_option autoImplicit false
open BuckPassing.Det

theorem solution {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (c : ι → (∀ i, X i) → ℝ) (Ψ : (∀ i, X i) → ℝ)
    (s : ∀ i, X i) (hpot : IsGenOrdPotential c Ψ)
    (hmin : ∀ i (x : X i), Ψ s ≤ Ψ (Function.update s i x)) :
    IsNash c s := by
  intro i x hlt
  exact absurd (hpot s i x hlt) (not_lt.mpr (hmin i x))
