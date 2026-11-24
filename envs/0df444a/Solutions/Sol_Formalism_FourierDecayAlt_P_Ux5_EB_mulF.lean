-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:40:52.293067+00:00
-- url     : https://prove2.me/submissions/34ff3c80-7272-44cc-b4cf-caa140059822

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mul

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
theorem _root_.solution {l n : Type*} {m : ℕ} {A : Matrix l (Fin m) ℂ} {B : Matrix (Fin m) n ℂ} {a b : ℝ}
    (hA : EB A a) (hB : EB B b) : EB (A * B) ((m : ℝ) * (a * b)) := by
  have := EB_mul hA hB
  rwa [Fintype.card_fin] at this
end Formalism.FourierDecayAlt.P.Ux5
