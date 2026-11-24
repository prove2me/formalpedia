-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.thetaF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:16.016265+00:00
-- url     : https://prove2.me/submissions/77281d20-0c08-47ac-86b6-225cd30c3aaa

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mulM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_levM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_heisF_meas

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : Measurable (thetaF k r') := by
  first
    | exact mulM_meas.comp ((levM_meas.comp measurable_snd).prodMk (heisF_meas.comp measurable_fst))
    | exact mulM_meas.comp ((levM_meas.comp measurable_snd).prod_mk (heisF_meas.comp measurable_fst))
end Formalism.FourierDecayAlt.P.LongWeylElement
