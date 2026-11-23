-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.EC.transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:07.70762+00:00
-- url     : https://prove2.me/submissions/2ac1bd41-3664-4336-992e-6b62d7fc3454

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Wd6
namespace EC
theorem _root_.solution {z : B} {M : M2 B} (hM : EC z M) : EC z Mᵀ := fun i j => hM j i
end EC
end Formalism.FourierDecayAlt.P.Wd6
