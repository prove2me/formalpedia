-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.localisation_typed_condition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:35.516376+00:00
-- url     : https://prove2.me/submissions/b321cf97-121e-415c-aaea-203c2358b065

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_localisation_typed_independent_exponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.LocTyped := by
  intro E _ _ _ g k ν _ hc P hP hgP
  ext t
  exact ⟨S6x6.localisation_typed_independent_exponent E g k ν 0 hc P hP hgP t, S6x6.localisation_typed_independent_exponent E g k 0 ν hc P hP hgP t⟩
end Formalism.FourierDecayAlt.P
