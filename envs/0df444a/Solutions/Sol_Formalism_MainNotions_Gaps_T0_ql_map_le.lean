-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.ql_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:16.862426+00:00
-- url     : https://prove2.me/submissions/06db969c-bd75-4844-b8e3-7dff94475249

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution (A S : Submodule O V) (f : V →ₗ[O] W) (P : Submodule O W) (h : S.map f ≤ P) :
    ql (A.map f) P ≤ ql A S := by
  let g : ↥A →ₗ[O] (↥(A.map f) ⧸ P.comap (A.map f).subtype) :=
    (P.comap (A.map f).subtype).mkQ ∘ₗ f.submoduleMap A
  have hk : S.comap A.subtype ≤ LinearMap.ker g := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (P.comap (A.map f).subtype).mkQ (f.submoduleMap A x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h ⟨x, hx, rfl⟩
  refine Module.length_le_of_surjective ((S.comap A.subtype).liftQ g hk) ?_
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, rfl⟩ := f.submoduleMap_surjective A z
  exact ⟨Submodule.Quotient.mk x, rfl⟩
end Formalism.MainNotions.Gaps.T0
