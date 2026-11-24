-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:07.047835+00:00
-- url     : https://prove2.me/submissions/727fe762-350a-4346-9121-64e68ee66f6e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_conjInv_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_radical_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.ConjInvRaw :=
  (B2x4.conjInv_of unipotent_radical_closed weyl_subgroup_closed weyl_subgroup_compact).1
end Formalism.FourierDecayAlt.P
