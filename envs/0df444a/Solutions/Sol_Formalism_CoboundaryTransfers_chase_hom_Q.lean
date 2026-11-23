-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.chase_hom_Q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:15.342464+00:00
-- url     : https://prove2.me/submissions/31c24b97-6bb5-4fc5-b757-be1fdbd48e87

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
theorem _root_.solution {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') {y : D}
    (hy : W.QInv y) : W'.QInv (f.f y) := by
  have hN : ∀ x ∈ W.N, f.f x ∈ W'.N := by
    cases f
    first | assumption | done
  show B.Q ^ M • f.f y ∈ W'.N
  rw [← map_smul f.f]
  exact hN _ hy
end Formalism.CoboundaryTransfers
