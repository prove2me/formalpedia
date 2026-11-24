-- Prove2me | solution 1 for Formalism.IncomingBounds.LatticeIndexAlt.isLat_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:10.245633+00:00
-- url     : https://prove2.me/submissions/4600ab13-d583-471c-98a9-43a1a122fcb2

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
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
namespace Formalism.IncomingBounds.LatticeIndexAlt
theorem _root_.solution {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (A B : Submodule O Y) (hA : A.FG) (hB : IsLat O K Y B) : IsLat O K Y (A ⊔ B) := by
  unfold IsLat at hB ⊢
  refine ⟨hA.sup hB.1, ?_⟩
  rw [eq_top_iff, ← hB.2]
  exact Submodule.span_mono (fun x hx => Submodule.mem_sup_right hx)
end Formalism.IncomingBounds.LatticeIndexAlt
