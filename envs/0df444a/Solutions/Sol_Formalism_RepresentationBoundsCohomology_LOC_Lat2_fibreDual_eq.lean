-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.fibreDual_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:14.10297+00:00
-- url     : https://prove2.me/submissions/240ce92c-0e83-4458-a7ec-45e80a3d1aca

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_zero_mem_fibre
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_pairB_apply

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
    (φ : Y →ₗ[O] VT ⧸ T) :
    fibreDual bY bT Y T φ = dualLat (pairB bY bT) (fibre Y T φ) := by
  ext ⟨f, g⟩
  constructor
  · rintro ⟨_, h2⟩ ⟨y, x⟩ ⟨hy, hφ⟩
    rw [pairB_apply]
    exact h2 ⟨y, hy⟩ x hφ
  · intro h
    refine ⟨fun x hx => ?_, fun y x hyx => ?_⟩
    · have := h (0, x) (zero_mem_fibre φ hx)
      rw [pairB_apply] at this
      simp only [map_zero, LinearMap.zero_apply, zero_sub] at this
      exact (Submodule.neg_mem_iff _).1 this
    · have := h (y, x) ⟨y.2, hyx⟩
      rw [pairB_apply] at this
      exact this
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
