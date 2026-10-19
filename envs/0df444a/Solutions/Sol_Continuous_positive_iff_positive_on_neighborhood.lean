-- Prove2me | solution 1 for Continuous.positive_iff_positive_on_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/b49a9027-4c06-4a7d-929e-d2fe4a7d4649

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
namespace Continuous
theorem _root_.solution {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hx
    refine ⟨{y | 0 < f y}, ?_, fun y hy => hy⟩
    exact (isOpen_lt continuous_const hf₁).mem_nhds hx
  · rintro ⟨U, hU, hpos⟩
    exact hpos x (mem_of_mem_nhds hU)
end Continuous
