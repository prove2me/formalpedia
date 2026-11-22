-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.EC.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:34.103952+00:00
-- url     : https://prove2.me/submissions/cd65efa6-b997-4295-96b4-50060f43f9a7

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
theorem _root_.solution {z : B} {M N : M2 B} (hM : EC z M) (hN : EC z N) : EC z (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun k _ => (hM i k).mul_right (hN k j)
end EC
end Formalism.FourierDecayAlt.P.Wd6
