-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.integral_wach_definitions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:31.651478+00:00
-- url     : https://prove2.me/submissions/0e0513a8-8457-4700-820c-80496482b27b

import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_IntegralWachDefinitions
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_cocycle_mem_Zf
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_cocycle_of_isCob1
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_mem_Z1_iff_cocycle
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_mem_coboundaries_of_isOneCoboundary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : IntDefs := by
  intro O A _ _ _ B M D _ _ _ _ W
  have h1 : ∀ y, y ∈ W.QInvSub ↔ W.QInv y := by
    intro y
    simp only [WachMod.QInvSub, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
      WachMod.QInv]
  have h2 : ∀ z, z ∈ W.XNSub ↔ W.XN z := by
    intro z
    simp only [WachMod.XNSub, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply,
      WachMod.XN]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  have h3 : ∀ y z, (y, z) ∈ W.ZInt ↔ W.Cocycle y z := by
    intro y z
    rw [WachMod.ZInt, Submodule.mem_inf, Submodule.mem_prod, Submodule.restrictScalars_mem,
      Submodule.restrictScalars_mem, h1, h2, W.mem_Z1_iff_cocycle]
    rfl
  have h4 : ∀ y z, (y, z) ∈ W.BInt ↔ W.IsCob1 y z := by
    intro y z
    have hf : ∀ x, ((W.φ - LinearMap.id).prod (W.γ - LinearMap.id)) x =
        (W.φ x - x, W.γ x - x) := fun _ => rfl
    rw [WachMod.BInt, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, hxe⟩
      rw [hf] at hxe
      obtain ⟨e1, e2⟩ := Prod.mk.inj hxe
      exact ⟨x, hx, e1.symm, e2.symm⟩
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨x, hx, hf x⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · rintro ⟨y, z⟩ h
    exact (h3 y z).2 (W.cocycle_of_isCob1 ((h4 y z).1 h))
  · rintro ⟨y, z⟩ h
    exact W.mem_coboundaries_of_isOneCoboundary ((h4 y z).1 h)
  · rintro ⟨y, z⟩ h
    exact W.cocycle_mem_Zf ((h3 y z).1 h)
end Formalism.CoboundaryTransfers
