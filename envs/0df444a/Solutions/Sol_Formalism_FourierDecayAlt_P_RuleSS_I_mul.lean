-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.I_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:28.277217+00:00
-- url     : https://prove2.me/submissions/ccc62d56-b57e-4023-8433-6b2f575ab598

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {h a a' b b' : A} (ha : a * h = h * a') (hb : b * h = h * b') :
    a * b * h = h * (a' * b') := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
end Formalism.FourierDecayAlt.P.RuleSS
