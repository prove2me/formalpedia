-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.wachModule_coboundaries_le_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:30.982256+00:00
-- url     : https://prove2.me/submissions/ccd2d70c-5f38-4482-a615-00ac1166e818

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachModule_mem_cocycles_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
open Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {Bw : Base O A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (W : WachMod Bw M D) : W.B1 ≤ W.Z1 := by
  intro pr hpr
  rw [wachModule_mem_cocycles_iff]
  unfold WachMod.B1 at hpr
  obtain ⟨d, rfl⟩ := hpr
  have key : W.γ (W.φ d) = W.φ (W.γ d) := by
    first
    | (cases W; simp_all)
    | (cases W; simp_all [LinearMap.ext_iff])
    | (cases W; simp_all [LinearMap.ext_iff, eq_comm])
  simp [key, Function.prod, map_add, map_sub, map_neg, neg_smul, LinearMap.add_apply] <;> abel
end Formalism.WeaklyAdmissibleFiltrations
