-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.chain_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:34.655803+00:00
-- url     : https://prove2.me/submissions/5f5457b2-042e-4dee-9400-1cb8f3351ec8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc

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
variable {p : ℕ} (G : GAtP p)
variable {G}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution {Fl : Fills G} (Lv : Levels Fl) : Nonempty (Chain Lv) := ⟨chainOf Lv⟩
end Formalism.MainNotions.G.Inhab
