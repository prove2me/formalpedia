-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.mnat2_convex_is_integrally_convex
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T02:44:16.977+00:00
-- url     : https://prove2.me/submissions/62737b12-7f4b-4f0a-af01-ff064bc23a01

import Mathlib
import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_mnat2_convex_set_is_integrally_convex
import Theorems.Thm_DiscreteConvex_ConjugacyDualityB_mnat2_convex_function_is_integrally_convex

open DiscreteConvex.ConjugacyDualityB

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → IsIntegrallyConvexFunction f) ∧
    (∀ D : Set (V → ℤ), MNat2ConvexSet D → IsIntegrallyConvex D) := by
  exact ⟨fun f hf => mnat2_convex_function_is_integrally_convex f hf,
    fun D hD => mnat2_convex_set_is_integrally_convex D hD⟩
