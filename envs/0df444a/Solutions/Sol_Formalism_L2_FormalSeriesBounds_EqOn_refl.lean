-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.EqOn.refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:41.97894+00:00
-- url     : https://prove2.me/submissions/b3a4f78e-45b1-4715-a20e-aed5b728b7fd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace EqOn
theorem _root_.solution (A : Set σ) (F : MvPowerSeries σ K) : EqOn A F F := fun _ _ => rfl
end EqOn
end Formalism.L2.FormalSeriesBounds
