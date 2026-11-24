-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.smul1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:42.348953+00:00
-- url     : https://prove2.me/submissions/eb7e144d-2155-43b8-bc24-9a30b9121315

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_map_line
import Theorems.Thm_Formalism_MainNotions_G_Inhab_homoth_val

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
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (γ : Multiplicative ℤ) (L : (places1 h).Tup) (n : ℤ)
    (hL : L (0 : Fin 1) = line W p n) :
    (level1 h).smul γ L (0 : Fin 1) = line W p (Multiplicative.toAdd γ + n) := by
  show Submodule.map ((Matrix.mulVecLin ((homoth h γ : GL (Fin 1) Qq) : Matrix (Fin 1) (Fin 1) Qq)).restrictScalars W)
    (L (0 : Fin 1)) = _
  rw [homoth_val, hL]
  exact map_line h _ _
end Formalism.MainNotions.G.Inhab
