-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.I_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:28.286928+00:00
-- url     : https://prove2.me/submissions/e725b4e0-d4fc-4759-86ab-cb297b4502ba

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
theorem _root_.solution {h k a a' a'' : A} (h1 : a * h = h * a') (h2 : a' * k = k * a'') :
    a * (h * k) = (h * k) * a'' := by
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
end Formalism.FourierDecayAlt.P.RuleSS
