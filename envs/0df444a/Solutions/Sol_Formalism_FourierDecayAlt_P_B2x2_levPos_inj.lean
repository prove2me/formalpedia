-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.levPos_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:45:00.145644+00:00
-- url     : https://prove2.me/submissions/07a45079-1437-4aa1-9a8f-de7ea061a02a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro s t h
  have h' : s.val + 1 = t.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)
end Formalism.FourierDecayAlt.P.B2x2
