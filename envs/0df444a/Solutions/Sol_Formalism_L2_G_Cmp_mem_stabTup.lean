-- Prove2me | solution 1 for Formalism.L2.G.Cmp.mem_stabTup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:28.749743+00:00
-- url     : https://prove2.me/submissions/56d653e6-28aa-4968-98ba-414b771c5060

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k nV : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (g : Fin nV → GL (Fin k) Qq) : g ∈ stabTup (nV := nV) (k := k) (Qq := Qq) W ↔ ∀ v, g v ∈ stabStd W := by
  show g ∈ Subgroup.pi Set.univ _ ↔ _
  simp [Subgroup.mem_pi]
end Formalism.L2.G.Cmp
