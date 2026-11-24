-- Prove2me | solution 1 for Formalism.IncomingBounds.LatticeIndexAlt.isLat_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:09.752833+00:00
-- url     : https://prove2.me/submissions/99b7e2fa-74ab-4aff-8be7-c1359e7785e4

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
    (c : K) (hc : c ≠ 0) (A : Submodule O Y) (hA : IsLat O K Y A) :
    IsLat O K Y (A.map ((c • LinearMap.id : Y →ₗ[K] Y).restrictScalars O)) := by
  unfold IsLat at hA ⊢
  refine ⟨hA.1.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hA.2, Submodule.map_top,
    LinearMap.range_eq_top]
  intro x
  refine ⟨c⁻¹ • x, ?_⟩
  simp [smul_smul, hc]
end Formalism.IncomingBounds.LatticeIndexAlt
