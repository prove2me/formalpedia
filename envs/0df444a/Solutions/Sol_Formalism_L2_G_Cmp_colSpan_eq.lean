-- Prove2me | solution 1 for Formalism.L2.G.Cmp.colSpan_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:31.492809+00:00
-- url     : https://prove2.me/submissions/876d0c46-b641-4902-877d-4e9ff7fe4428

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
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (g : GL (Fin k) Qq) : colSpan W (g : Matrix (Fin k) (Fin k) Qq) = gMap W g (stdL W) := by
  unfold gMap stdL colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  refine congrArg Set.range (funext fun c => funext fun i => ?_)
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
end Formalism.L2.G.Cmp
