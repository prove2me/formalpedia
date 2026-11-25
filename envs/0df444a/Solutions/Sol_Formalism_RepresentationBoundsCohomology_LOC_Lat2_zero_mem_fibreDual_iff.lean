-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.zero_mem_fibreDual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:20.164484+00:00
-- url     : https://prove2.me/submissions/010553c4-1bab-4cec-b7cc-d7959d26f86c

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
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) (g : VY') :
    ((0 : VT'), g) ∈ fibreDual bY bT Y T φ ↔ g ∈ dualLat bY Y := by
  constructor
  · rintro ⟨_, h⟩ y hy
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective T (φ ⟨y, hy⟩)
    have := h ⟨y, hy⟩ x hx.symm
    simpa using this
  · intro h
    refine ⟨Submodule.zero_mem _, fun y x _ => ?_⟩
    have := h y y.2
    simpa using this
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
