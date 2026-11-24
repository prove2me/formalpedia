-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.mx_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:02:20.678769+00:00
-- url     : https://prove2.me/submissions/7537f2ba-5587-43ee-b735-75eef5eadcac

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
theorem _root_.solution {m n : Type*} [Fintype m] [Fintype n] {A : Matrix m n ℂ} {c : ℝ} (h : EB A c) (hc : 0 ≤ c) :
    mx A ≤ c := by
  unfold mx
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => ?_
  exact h i j
end Formalism.FourierDecayAlt.P.Ux5
