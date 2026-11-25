-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.gat_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:48.104002+00:00
-- url     : https://prove2.me/submissions/8997d1a6-c919-4839-b500-47ea1f8c93b5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_gat_of_setting
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a


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
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ Nonempty G.comp ∧ G.TrivStab ∧ G.FinClasses :=
  haveI : Fact p.Prime := ⟨hp⟩
  gat_of_setting (Formalism.BasicNotions.Examples₂.LevelValuationRings.hidaSettingOfEven p 2 h5 le_rfl even_two)
end Formalism.MainNotions.G.Inhab
