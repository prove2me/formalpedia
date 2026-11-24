-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.invM_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:53:01.857797+00:00
-- url     : https://prove2.me/submissions/ae4ec914-c237-4fbd-a1e5-07bf4da63510

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_detF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_adjF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_invM_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_adjF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_detF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_invM_smul


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
theorem _root_.solution : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]
  first
    | exact (detF_cont.measurable.inv).smul adjF_cont.measurable
    | exact (measurable_inv.comp detF_cont.measurable).smul adjF_cont.measurable
    | fun_prop
end Formalism.FourierDecayAlt.P.LongWeylElement
