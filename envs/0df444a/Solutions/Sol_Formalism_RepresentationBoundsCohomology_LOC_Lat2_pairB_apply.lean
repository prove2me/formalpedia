-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.pairB_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:37.96248+00:00
-- url     : https://prove2.me/submissions/e4492774-31f9-4bcf-a459-4277964b620a

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
open Lat2
open Formalism.RepresentationBoundsCohomology.LOC.Lat2
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {VY VT VY' VT' : Type u}
  [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY] [IsScalarTower O (FractionRing O) VY]
  [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']
omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT]
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (p : VY × VT) (q : VT' × VY') :
    pairB bY bT p q = bY p.1 q.2 - bT p.2 q.1 := rfl
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
