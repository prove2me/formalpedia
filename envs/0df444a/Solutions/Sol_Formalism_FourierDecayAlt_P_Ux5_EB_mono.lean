-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:51:28.341483+00:00
-- url     : https://prove2.me/submissions/035011d5-3882-4fc1-8a12-242c1272ee8c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
namespace EB
theorem _root_.solution {m n : Type*} {A : Matrix m n ℂ} {a b : ℝ} (h : EB A a) (hab : a ≤ b) : EB A b :=
  fun i j => (h i j).trans hab
end EB
end Formalism.FourierDecayAlt.P.Ux5
