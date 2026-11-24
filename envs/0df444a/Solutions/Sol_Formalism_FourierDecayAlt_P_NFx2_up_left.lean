-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.up_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:47.318798+00:00
-- url     : https://prove2.me/submissions/8af76a64-c1dc-42f4-8af6-63885b2e5413

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
open Formalism.FourierDecayAlt.M
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (P : M.Par) {l : ℕ} {π π' σ : M.Ty P} (h : M.Up P l π σ) (h' : M.Up P l π' σ) : π = π' := by
  funext i; apply Fin.ext; have := h i; have := h' i; omega
end Formalism.FourierDecayAlt.P.NFx2
