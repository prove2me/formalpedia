-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.cell_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:08.341573+00:00
-- url     : https://prove2.me/submissions/271415e4-efb7-4b3c-927a-aa3819becf24

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mm_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_invM_meas


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
theorem _root_.solution {α : Type*} [MeasurableSpace α] {N T M N' : α → Mt k r} (hN : Measurable N) (hT : Measurable T)
    (hM : Measurable M) (hN' : Measurable N') :
    Measurable (β := Mt k r) (fun t => ((Matrix.of (N t))⁻¹ * Matrix.of (T t) * Matrix.of (M t) * Matrix.of (N' t) : Mat k r)) := by
  exact mm_meas (mm_meas (mm_meas (invM_meas.comp hN) hT) hM) hN'
end Formalism.FourierDecayAlt.P.LongWeylElement
