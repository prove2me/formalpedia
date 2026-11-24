-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.entry_le_mx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:40.249278+00:00
-- url     : https://prove2.me/submissions/75dceca0-370f-4587-8f4f-dad1a490b5e5

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
theorem _root_.solution {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (i : m) (j : n) :
    ‖A i j‖ ≤ mx A := by
  unfold mx
  exact (norm_le_pi_norm (Matrix.of.symm A i) j).trans (norm_le_pi_norm (Matrix.of.symm A) i)
end Formalism.FourierDecayAlt.P.Ux5
