-- Prove2me | solution 2 for Continuous.positive_iff_positive_on_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:06.868318+00:00
-- url     : https://prove2.me/submissions/837fba92-18dc-4992-916b-9fdcbd675246

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
variable {E : Type*} [TopologicalSpace E]


theorem solution {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y := by
  constructor
  · intro h
    exact ⟨_, hf₁.continuousAt.preimage_mem_nhds (Ioi_mem_nhds h), fun y hy => hy⟩
  · rintro ⟨U, hU, h⟩
    exact h x (mem_of_mem_nhds hU)

