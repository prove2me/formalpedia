-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.isOneCochain_diffZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:04.472183+00:00
-- url     : https://prove2.me/submissions/a51068a3-7072-4a6e-9f56-f45c992777c6

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary

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
theorem _root_.solution {x : D} (hx : x ∈ W.N) : W.C1 (W.φ x - x) (W.γ x - x) := by
  refine ⟨?_, ?_⟩
  · simp only [QInv, smul_sub]
    exact W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)
  · obtain ⟨x', hx', h⟩ := W.γ_N x hx
    exact ⟨x', hx', h⟩
end Formalism.CoboundaryTransfers.WachMod
