-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.map_invM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:25.514996+00:00
-- url     : https://prove2.me/submissions/a462ab36-b6b2-4e08-bb82-d7599dacb380

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_haar_measure_inversion


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
theorem _root_.solution {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : B.IsHaarOn U μ) : μ.map B2.invM = μ := Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU hμ
end Formalism.FourierDecayAlt.P.S3dx4
