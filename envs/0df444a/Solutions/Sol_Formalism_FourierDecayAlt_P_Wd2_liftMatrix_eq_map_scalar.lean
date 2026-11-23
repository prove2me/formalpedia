-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.liftMatrix_eq_map_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:44.45845+00:00
-- url     : https://prove2.me/submissions/d21d7a72-b462-44b2-b37c-e20883a6397b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A)) = M.map (Matrix.scalar (Ix S)) := rfl
end Formalism.FourierDecayAlt.P.Wd2
