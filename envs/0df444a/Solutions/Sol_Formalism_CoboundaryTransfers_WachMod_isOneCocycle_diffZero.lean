-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.isOneCocycle_diffZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:05.493036+00:00
-- url     : https://prove2.me/submissions/816d6640-c4b7-4dab-adf9-0de9a86d4fed

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_diffOne_diffZero
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_isOneCochain_diffZero

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
theorem _root_.solution {x : D} (hx : x ∈ W.N) : W.Cocycle (W.φ x - x) (W.γ x - x) :=
  ⟨W.isOneCochain_diffZero hx, W.diffOne_diffZero x⟩
end Formalism.CoboundaryTransfers.WachMod
