-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.relIsCoreNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:42.854407+00:00
-- url     : https://prove2.me/submissions/bc4332da-86dc-41e1-a8cf-aedd27524047

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
theorem _root_.solution : RelIsCoreNorm := by
  intro P A _ _ _ d
  unfold Q.NFData.Rel RelCore RelNorm
  constructor
  · rintro ⟨a, b, c, e, f, g⟩; exact ⟨⟨a, b, c, e, f⟩, g⟩
  · rintro ⟨⟨a, b, c, e, f⟩, g⟩; exact ⟨a, b, c, e, f, g⟩
end Formalism.FourierDecayAlt.P.NFx2
