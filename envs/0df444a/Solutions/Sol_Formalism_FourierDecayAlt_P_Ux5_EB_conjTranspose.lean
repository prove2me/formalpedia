-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:02:18.769149+00:00
-- url     : https://prove2.me/submissions/0d571b99-5550-4e06-9b34-508a3e3b9b4b

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
theorem _root_.solution {m n : Type*} {A : Matrix m n ℂ} {a : ℝ} (h : EB A a) : EB Aᴴ a := by
  intro i j
  simpa [conjTranspose_apply, norm_star] using h j i
end Formalism.FourierDecayAlt.P.Ux5
