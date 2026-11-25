-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:23.888797+00:00
-- url     : https://prove2.me/submissions/62aaf83e-8b36-4807-9a81-518866110912

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
theorem _root_.solution (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a) G = a * constantCoeff G := by
  by_cases ha : a = 0
  · subst ha
    simp [jetAt0]
  · simp [jetAt0, MvPolynomial.support_C, ha, mfact, MvPowerSeries.coeff_zero_eq_constantCoeff]
end Formalism.L2.FormalSeriesBounds
