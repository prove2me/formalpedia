-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.mid_levPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:10.625665+00:00
-- url     : https://prove2.me/submissions/2f96ae72-4a09-41bf-994a-059a0323a426

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
theorem _root_.solution (k r' : ℕ) (s : Fin (2 * r' + k + 1)) : mid k r' (levPos k 1 r' s) := by
  have hs := s.isLt
  show 1 ≤ s.val + 1 ∧ s.val + 1 < 2 * r' + k + 1 + 1
  constructor <;> omega
end Formalism.FourierDecayAlt.P.B2x2
