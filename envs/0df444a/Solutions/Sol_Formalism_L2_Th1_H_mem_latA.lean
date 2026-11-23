-- Prove2me | solution 1 for Formalism.L2.Th1.H.mem_latA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:33.864141+00:00
-- url     : https://prove2.me/submissions/024b6652-569b-4978-a931-df35d44c9522

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution {x : V} : x ∈ latA Λ δ Ae ↔ ∃ w ∈ Λ, δ w ∈ Λ ∧ Ae (δ w) = x := by
  simp only [latA, imgLat, AddSubgroup.mem_map, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨z, ⟨hz, w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, hz, rfl⟩
  · rintro ⟨w, hw, hδ, rfl⟩
    exact ⟨δ w, ⟨hδ, w, hw, rfl⟩, rfl⟩
end Formalism.L2.Th1.H
