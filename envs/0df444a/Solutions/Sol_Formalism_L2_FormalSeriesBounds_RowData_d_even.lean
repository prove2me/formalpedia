-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowData.d_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:08:44.755742+00:00
-- url     : https://prove2.me/submissions/56e4bfd9-787b-492b-90d0-75d5b4f3b01d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface

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
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RowData
variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
  [∀ g, Fintype (J g)] (X : RowData C V d I J)
namespace Formalism.L2.FormalSeriesBounds.RowData
theorem _root_.solution (h : X.Alt) : Even d := h.1
end Formalism.L2.FormalSeriesBounds.RowData
