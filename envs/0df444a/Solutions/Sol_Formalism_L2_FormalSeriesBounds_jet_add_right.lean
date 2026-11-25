-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:17.735593+00:00
-- url     : https://prove2.me/submissions/d46054d5-f963-4a22-ab0b-2281d3586b38

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
theorem _root_.solution (P : MvPolynomial σ C) (G H : MvPowerSeries σ C) :
    jetAt0 P (G + H) = jetAt0 P G + jetAt0 P H := by
  simp only [jetAt0, map_add, mul_add, Finset.sum_add_distrib]
end Formalism.L2.FormalSeriesBounds
