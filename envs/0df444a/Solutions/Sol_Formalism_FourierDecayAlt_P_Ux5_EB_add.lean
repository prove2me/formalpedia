-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:26:04.605225+00:00
-- url     : https://prove2.me/submissions/cc52eb0e-60a1-42c0-9b01-9910e8cfe9d4

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
theorem _root_.solution {m n : Type*} {A B : Matrix m n ℂ} {a b : ℝ} (hA : EB A a) (hB : EB B b) :
    EB (A + B) (a + b) :=
  fun i j => (norm_add_le _ _).trans (add_le_add (hA i j) (hB i j))
end Formalism.FourierDecayAlt.P.Ux5
