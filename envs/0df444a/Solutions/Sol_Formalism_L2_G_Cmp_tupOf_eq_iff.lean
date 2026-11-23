-- Prove2me | solution 1 for Formalism.L2.G.Cmp.tupOf_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:53.520317+00:00
-- url     : https://prove2.me/submissions/800e0a74-00a1-45eb-a87c-ad3e0418f060

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_L2_G_Cmp_gMap_std_eq_iff
import Theorems.Thm_Formalism_L2_G_Cmp_mem_stabTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k nV : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (g h : Fin nV → GL (Fin k) Qq) :
    tupOf W g = tupOf W h ↔ h⁻¹ * g ∈ stabTup (nV := nV) (k := k) (Qq := Qq) W := by
  rw [mem_stabTup]
  constructor
  · intro H v
    exact (gMap_std_eq_iff W (g v) (h v)).1 (congrFun H v)
  · intro H
    funext v
    exact (gMap_std_eq_iff W (g v) (h v)).2 (H v)
end Formalism.L2.G.Cmp
