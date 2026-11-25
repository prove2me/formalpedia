-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.fills_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:45.03402+00:00
-- url     : https://prove2.me/submissions/fc135ffc-fac3-4def-bbd3-4d42920716eb

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
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (TT : ∀ v : Fin G.P.nV, Finset (Fin (G.P.n' v))) (t mm : ℕ) :
    ∃ Fl : Fills G, Fl.TT = TT ∧ Fl.t = t ∧ Fl.mm = mm := ⟨fillsOf G TT t mm, rfl, rfl, rfl⟩
end Formalism.MainNotions.G.Inhab
