-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.ioR_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:11.439035+00:00
-- url     : https://prove2.me/submissions/3afc38b1-8d3e-4ee8-98d6-576b9fb9b9e3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (M : Matrix (Ty P) (Ty P) ℝ) (a b : Ty P) :
    ioR P M a b = algebraMap ℂ (Pr P.r) ((M a b : ℝ) : ℂ) := rfl
end Formalism.FourierDecayAlt.P.Mx4
