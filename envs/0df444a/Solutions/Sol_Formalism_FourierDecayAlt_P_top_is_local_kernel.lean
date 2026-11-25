-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_is_local_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:26.140674+00:00
-- url     : https://prove2.me/submissions/434c4ece-179b-405b-9c50-9041c5959956

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.TopIsLocalKernel := by
  intro K _ R ψ E α _ m σ u τ₀ η Θ hΘ t c hc h h' hh hh'
  have e : (topSys R ψ σ u τ₀ η Θ).N t t h h' = Θ ((u : K) * σ t - τ₀) (η h) (η h') := by
    simp [topSys]
  rw [e, ← hc]
  exact hΘ c (η h) (η h') hh hh'
end Formalism.FourierDecayAlt.P
