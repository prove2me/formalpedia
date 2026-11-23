-- Prove2me | solution 1 for Formalism.L2.G.Cmp.mem_stabStd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:28.719456+00:00
-- url     : https://prove2.me/submissions/f9c1e49e-c395-4020-a263-6aeac02a8a2e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat

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
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (g : GL (Fin k) Qq) : g ∈ stabStd (k := k) (Qq := Qq) W ↔ gMap W g (stdL W) = stdL W := Iff.rfl
end Formalism.L2.G.Cmp
