-- Prove2me | solution 1 for Formalism.L2.G.Cmp.tupOf_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:46.339797+00:00
-- url     : https://prove2.me/submissions/7dca7076-d2e7-45cc-b2e6-c037f6da9994

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_L2_G_Cmp_isLattice_iff

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
theorem _root_.solution (g : Fin nV → GL (Fin k) Qq) (v : Fin nV) : IsLattice W (tupOf W g v) := (isLattice_iff W _).2 ⟨g v, rfl⟩
end Formalism.L2.G.Cmp
