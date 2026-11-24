-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.gat_of_setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:46.770022+00:00
-- url     : https://prove2.me/submissions/bb202693-c6b3-48fd-a89d-ead5bf44583e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_level1_trivStab
import Theorems.Thm_Formalism_MainNotions_G_Inhab_level1_finClasses

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
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ Nonempty G.comp ∧ G.TrivStab ∧ G.FinClasses :=
  ⟨gat1 h, le_rfl, ⟨()⟩, fun _ => level1_trivStab h, fun _ => level1_finClasses h⟩
end Formalism.MainNotions.G.Inhab
