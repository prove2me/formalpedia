-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_ball_volume_crude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:38.859312+00:00
-- url     : https://prove2.me/submissions/e580a027-8442-43df-a56d-b531b04fef67

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gFromDiag__623203fd9e2d
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts
import Theorems.Thm_Formalism_QuantumDeterminants_uHConj
import Theorems.Thm_Formalism_REAL_uJEmb
import Theorems.Thm_Formalism_REAL_unimodular
import Theorems.Thm_Formalism_REAL_volGrowth


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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.VolCrude :=
  (HaarUniquenessConjugation.gFromDiag' uJEmb unimodular volGrowth hpkFacts uHConj).2
end Formalism.FourierDecayAlt.P
