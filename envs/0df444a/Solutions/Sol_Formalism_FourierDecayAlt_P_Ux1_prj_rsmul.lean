-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.prj_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:13:40.599114+00:00
-- url     : https://prove2.me/submissions/0313a682-177a-43e0-a6e9-734d97cae454

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel

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
theorem _root_.solution (c : ℝ) (Z : Mat k r) : prj (c • Z) = c • prj Z := by
  unfold prj
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c Z, RCLike.real_smul_eq_coe_smul (K := ℂ) c,
    conjTranspose_smul]
  simp only [RCLike.star_def, RCLike.conj_ofReal]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul, smul_smul]
  congr 1; ring
end Formalism.FourierDecayAlt.P.Ux1
