-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.isPF_smul_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:19:49.579035+00:00
-- url     : https://prove2.me/submissions/34e3a8ba-9172-4c00-b809-4886e1edeb90

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_cpoly

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
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {f : ℂ → A} (Q : ℂ[X]) (hf : IsPF f) : IsPF fun Y => Q.eval Y • f Y := by
  have := isPF_mul (isPF_cpoly Q (1 : A)) hf
  simpa [smul_mul_assoc] using this
end Formalism.FourierDecayAlt.P.NFx2
