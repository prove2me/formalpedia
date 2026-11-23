-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.line_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:52.794858+00:00
-- url     : https://prove2.me/submissions/12e6cfae-f172-494e-becb-efb4c7504db9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_colSpan_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (n : ℤ) : IsLattice W (line W (Qq := Qq) p n) := by
  refine ⟨Matrix.of fun _ _ => (p : Qq) ^ n, ?_, ?_⟩
  · rw [Matrix.det_fin_one]
    exact (zpow_ne_zero _ (p_ne h)).isUnit
  · rw [colSpan_one]; rfl
end Formalism.MainNotions.G.Inhab
