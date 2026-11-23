-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.wachModule_mem_cocycles_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:16.122802+00:00
-- url     : https://prove2.me/submissions/dc74d30d-7138-4619-a1a9-847096f47de0

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol

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
theorem _root_.solution (W : WachMod Bw M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ (W.γ pr.1 - pr.1) - (W.φ pr.2 - pr.2) = 0 := by
  unfold WachMod.Z1
  simp
  rw [← neg_sub (W.φ pr.2) pr.2, ← sub_eq_add_neg]
end Formalism.WeaklyAdmissibleFiltrations
