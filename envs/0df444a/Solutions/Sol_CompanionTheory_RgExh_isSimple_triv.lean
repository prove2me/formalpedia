-- Prove2me | solution 1 for CompanionTheory.RgExh.isSimple_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:16.260314+00:00
-- url     : https://prove2.me/submissions/39b55800-8d62-48fd-949e-e4ba63f2896d

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_IsSimpleTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
attribute [instance] GMod.acg GMod.mod
namespace CompanionTheory.RgExh
theorem _root_.solution : IsSimple (triv n) := ⟨inferInstanceAs (Nontrivial ℂ), fun S _ => eq_bot_or_eq_top (α := Submodule ℂ ℂ) S⟩
end CompanionTheory.RgExh
