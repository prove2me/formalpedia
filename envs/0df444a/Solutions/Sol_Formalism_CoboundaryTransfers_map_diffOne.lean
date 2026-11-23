-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.map_diffOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:30.171313+00:00
-- url     : https://prove2.me/submissions/e8e88792-ffe2-44f6-b95d-b8c719600a77

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
theorem _root_.solution {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') (y z : D) :
    f.f (W.d1 y z) = W'.d1 (f.f y) (f.f z) := by
  have hφ : ∀ x, f.f (W.φ x) = W'.φ (f.f x) := by
    cases f
    first | assumption | done
  have hγ : ∀ x, f.f (W.γ x) = W'.γ (f.f x) := by
    cases f
    first | assumption | done
  simp only [WachMod.d1, map_sub, hφ, hγ]
end Formalism.CoboundaryTransfers
