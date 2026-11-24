-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.wachHom_prodMap_mem_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:15.105081+00:00
-- url     : https://prove2.me/submissions/37bc9685-b9cb-4cf3-970b-13997755cf0e

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
theorem _root_.solution {W : WachMod Bw M D} {W' : WachMod Bw M D'} (Fw : Hom W W') (pr : D × D)
    (h : pr ∈ W.Z1) : Fw.f2 pr ∈ W'.Z1 := by
  rw [wachModule_mem_cocycles_iff] at h ⊢
  have := congrArg Fw.f h
  simp only [map_sub, map_zero, Fw.φ_comm, Fw.γ_comm] at this
  exact this
end Formalism.WeaklyAdmissibleFiltrations
