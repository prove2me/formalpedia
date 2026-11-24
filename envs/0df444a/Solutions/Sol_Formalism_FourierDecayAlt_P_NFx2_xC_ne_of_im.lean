-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.xC_ne_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:50.871159+00:00
-- url     : https://prove2.me/submissions/03bb9e43-5445-4759-aa17-3b469e72f748

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (P : M.Par) (ρ : M.Ty P) {Y : ℂ} (h : Y.im ≠ 0) : M.xC P ρ Y ≠ 0 := by
  unfold M.xC
  rw [Finset.prod_ne_zero_iff]
  intro i _ h0
  apply h
  have := congrArg Complex.im h0
  simpa using this
end Formalism.FourierDecayAlt.P.NFx2
