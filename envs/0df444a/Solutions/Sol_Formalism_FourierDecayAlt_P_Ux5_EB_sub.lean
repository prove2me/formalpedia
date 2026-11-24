-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:23.172129+00:00
-- url     : https://prove2.me/submissions/f9af7665-1ddf-4b75-81ce-44815323e6cb

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_neg

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
    EB (A - B) (a + b) := by
  rw [sub_eq_add_neg]
  exact EB_add hA (EB_neg hB)
end Formalism.FourierDecayAlt.P.Ux5
