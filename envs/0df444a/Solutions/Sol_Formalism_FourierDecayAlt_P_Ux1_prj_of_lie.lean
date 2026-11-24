-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.prj_of_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:53.858517+00:00
-- url     : https://prove2.me/submissions/d7e158ff-3e16-47b4-b51c-2ea6c9130896

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux1_hpk_sq__7d0cb96087ff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {Z : Mat k r} (hZ : inLie k r Z) : prj Z = Z := by
  unfold prj
  have h0 : Zᴴ * Hpk k r = -(Hpk k r * Z) := eq_neg_of_add_eq_zero_left hZ
  have h1 : Hpk k r * Zᴴ * Hpk k r = -Z := by
    rw [Matrix.mul_assoc, h0, Matrix.mul_neg, ← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
  rw [h1, sub_neg_eq_add, ← two_smul ℂ Z, smul_smul]
  norm_num
end Formalism.FourierDecayAlt.P.Ux1
