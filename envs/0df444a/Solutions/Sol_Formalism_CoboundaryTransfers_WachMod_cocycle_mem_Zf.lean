-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.cocycle_mem_Zf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:52.250066+00:00
-- url     : https://prove2.me/submissions/87fd9d6e-ef36-4b87-958b-5251e5e3795a

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_mem_cocycles_of_isOneCocycle

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
open Formalism.CoboundaryTransfers.WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)
namespace Formalism.CoboundaryTransfers.WachMod
theorem _root_.solution {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Zf := by
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨W.mem_cocycles_of_isOneCocycle h, 0, 0,
    W.B1.zero_mem, ?_⟩)
  simp only [pow_zero, one_smul, add_zero]
  exact ⟨⟨M, h.1.1⟩, h.1.2⟩
end Formalism.CoboundaryTransfers.WachMod
