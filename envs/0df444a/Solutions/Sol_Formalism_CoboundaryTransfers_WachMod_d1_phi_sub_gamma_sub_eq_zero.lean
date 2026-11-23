-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod_d1_phi_sub_gamma_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:06.292904+00:00
-- url     : https://prove2.me/submissions/583a1476-65a2-4e63-bfe9-10344027aa38

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower

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
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  have hc : ∀ y : D, W.φ (W.γ y) = W.γ (W.φ y) := by
    cases W
    assumption
  simp only [WachMod.d1, map_sub, hc]
  abel
end Formalism.CoboundaryTransfers
