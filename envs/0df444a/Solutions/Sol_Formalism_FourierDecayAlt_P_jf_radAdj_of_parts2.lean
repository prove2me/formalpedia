-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_radAdj_of_parts2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:59.809187+00:00
-- url     : https://prove2.me/submissions/3a9edf42-477e-4e0c-b9a7-11391385208f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_betaAdjC_of_lemmaBNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_radAdj_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.B2.LemmaBNorm → Formalism.FourierDecayAlt.JF.RadAdj := fun hE hD hA hL =>
  jf_radAdj_of_parts hE hD hA (jf_betaAdjC_of_lemmaBNorm hL)
end Formalism.FourierDecayAlt.P
