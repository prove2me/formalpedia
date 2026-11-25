-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.measurable_componentwiseInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:40.133057+00:00
-- url     : https://prove2.me/submissions/157d8a62-a67d-4b84-95bd-5ba5fbb8a78b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_invM_meas


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution : Measurable (invP (k := k) (r := r)) := by
  have h := B2x1.invM_meas (k := k) (r := r)
  exact (h.prodMap h).prodMap (h.prodMap h)
end Formalism.FourierDecayAlt.P.S3dx4
