-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:30.394862+00:00
-- url     : https://prove2.me/submissions/7303b5db-e828-482b-a902-06c7cf86c9c9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet

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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (P : MvPolynomial σ C) : jetAt0 P (0 : MvPowerSeries σ C) = 0 := by
  simp [jetAt0]
end Formalism.L2.FormalSeriesBounds
