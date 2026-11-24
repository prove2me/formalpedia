-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.up_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:43:56.217428+00:00
-- url     : https://prove2.me/submissions/b5131657-fa7d-45a2-ac64-d4109f8cd810

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
theorem _root_.solution (P : M.Par) {l : ℕ} {π σ σ' : M.Ty P} (h : M.Up P l π σ) (h' : M.Up P l π σ') : σ = σ' := by
  funext i; apply Fin.ext; rw [h i, h' i]
end Formalism.FourierDecayAlt.P.NFx2
