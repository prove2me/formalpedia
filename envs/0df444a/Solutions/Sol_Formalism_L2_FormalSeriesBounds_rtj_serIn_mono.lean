-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_serIn_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:39.878297+00:00
-- url     : https://prove2.me/submissions/b44db0e6-3c00-4e41-a94b-e35a7de25b7c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

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
theorem _root_.solution {A B : Set σ} (h : A ⊆ B) {F : MvPowerSeries σ K} (hF : rtjSerIn A F) :
    rtjSerIn B F := by
  unfold rtjSerIn at hF ⊢
  intro μ hμ
  exact (hF μ hμ).trans h
end Formalism.L2.FormalSeriesBounds
