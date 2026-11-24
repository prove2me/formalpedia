-- Prove2me | solution 1 for Formalism.IncomingBounds.LatticeIndexAlt.map_comap_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:10.299189+00:00
-- url     : https://prove2.me/submissions/62f764b7-4b4d-466c-98d1-42b26b809dfe

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.LatticeIndexAlt
open Formalism.LatticeIndexTer
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]
namespace Formalism.IncomingBounds.LatticeIndexAlt
theorem _root_.solution (W : Submodule K X) (A : Submodule O X) :
    (A.comap ((W.subtype).restrictScalars O)).map ((W.subtype).restrictScalars O) =
      A ⊓ W.restrictScalars O := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hW⟩
    exact ⟨⟨x, hW⟩, hx, rfl⟩
end Formalism.IncomingBounds.LatticeIndexAlt
