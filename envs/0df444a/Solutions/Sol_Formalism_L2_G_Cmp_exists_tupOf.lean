-- Prove2me | solution 1 for Formalism.L2.G.Cmp.exists_tupOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:37.378671+00:00
-- url     : https://prove2.me/submissions/69b38fa9-b56c-482b-9379-8f4abd644080

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
theorem _root_.solution (L : Fin nV → Submodule W (Fin k → Qq)) (hL : ∀ v, IsLattice W (L v)) : ∃ g, L = tupOf W g := by
  choose g hg using fun v => (isLattice_iff W (L v)).1 (hL v)
  exact ⟨g, funext hg⟩
end Formalism.L2.G.Cmp
