-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.zero_mem_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:39.154263+00:00
-- url     : https://prove2.me/submissions/3127d772-f97c-416c-832e-e54142f85146

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
omit [IsDomain O] [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT]
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution {Y : Submodule O VY} {T : Submodule O VT} (φ : Y →ₗ[O] VT ⧸ T) {x : VT}
    (hx : x ∈ T) : ((0 : VY), x) ∈ fibre Y T φ := by
  refine ⟨Y.zero_mem, ?_⟩
  have : (⟨((0 : VY), x).1, Y.zero_mem⟩ : Y) = 0 := rfl
  rw [this, map_zero]
  exact ((Submodule.Quotient.mk_eq_zero T).2 hx).symm
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
