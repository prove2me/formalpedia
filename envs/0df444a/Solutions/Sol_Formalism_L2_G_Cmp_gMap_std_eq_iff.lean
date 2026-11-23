-- Prove2me | solution 1 for Formalism.L2.G.Cmp.gMap_std_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:50.120802+00:00
-- url     : https://prove2.me/submissions/b2cfb0fe-3364-4de1-97e4-94dd8d8f5b2e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_L2_G_Cmp_mem_stabStd

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
theorem _root_.solution (g h : GL (Fin k) Qq) :
    gMap W g (stdL W) = gMap W h (stdL W) ↔ h⁻¹ * g ∈ stabStd (k := k) (Qq := Qq) W := by
  rw [mem_stabStd, gMap_mul]
  constructor
  · intro e
    rw [e, ← gMap_mul, inv_mul_cancel, gMap_one]
  · intro e
    apply gMap_inj W h⁻¹
    rw [e, ← gMap_mul, inv_mul_cancel, gMap_one]
end Formalism.L2.G.Cmp
