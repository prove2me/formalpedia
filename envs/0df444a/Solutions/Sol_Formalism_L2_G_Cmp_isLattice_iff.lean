-- Prove2me | solution 1 for Formalism.L2.G.Cmp.isLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:51.885803+00:00
-- url     : https://prove2.me/submissions/3abfc793-431f-487d-bc47-3a7a3b13a480

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_L2_G_Cmp_colSpan_eq

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
theorem _root_.solution (L : Submodule W (Fin k → Qq)) : IsLattice W L ↔ ∃ g : GL (Fin k) Qq, L = gMap W g (stdL W) := by
  constructor
  · rintro ⟨g, hg, hL⟩
    let G : GL (Fin k) Qq := Units.mk g g⁻¹ (Matrix.mul_nonsing_inv g hg) (Matrix.nonsing_inv_mul g hg)
    have hG : (G : Matrix (Fin k) (Fin k) Qq) = g := rfl
    refine ⟨G, ?_⟩
    rw [hL, ← colSpan_eq, hG]
  · rintro ⟨g, hL⟩
    refine ⟨(g : Matrix (Fin k) (Fin k) Qq), (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, ?_⟩
    rw [hL, colSpan_eq]
end Formalism.L2.G.Cmp
