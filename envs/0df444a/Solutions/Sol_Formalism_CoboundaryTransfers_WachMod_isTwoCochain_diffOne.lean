-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.isTwoCochain_diffOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:17.80943+00:00
-- url     : https://prove2.me/submissions/12ed7adb-751d-44fc-8b0d-c476695601d3

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_qInv_of_mem
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_qInv_sub

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
theorem _root_.solution {y z : D} (h : W.C1 y z) : W.C2 (W.d1 y z) := by
  obtain ⟨hy, n, hn, rfl⟩ := h
  obtain ⟨y', hy', hγ⟩ := W.γ_QN y hy
  obtain ⟨v, hv⟩ := B.φX
  refine ⟨y' - (v • W.φ n - n), ?_, ?_⟩
  · refine W.qInv_sub hy' (W.qInv_sub ?_ (W.qInv_of_mem hn))
    refine W.qInv_smul v ?_
    exact W.φ_N n hn
  · rw [d1, hγ, W.φ_smul, hv, mul_smul, smul_sub, smul_sub]
end Formalism.CoboundaryTransfers.WachMod
