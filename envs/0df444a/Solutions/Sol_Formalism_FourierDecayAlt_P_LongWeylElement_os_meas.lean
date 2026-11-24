-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.os_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:15.356375+00:00
-- url     : https://prove2.me/submissions/f5a0af23-d430-4db6-baef-29d4713197aa

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mm_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_levM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_heisF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_long_weyl_element_measurable
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
theorem _root_.solution {α : Type*} [MeasurableSpace α] {X X' : α → HPar k r'} {C : α → ℂ} {Gm : α → Mt k r'}
    (hX : Measurable X) (hC : Measurable C) (hG : Measurable Gm) (hX' : Measurable X') :
    Measurable (β := Mt k (1 + r')) (fun t => oneStep k r' (X t) (C t) (Matrix.of (Gm t)) (X' t)) := by
  exact mm_meas (mm_meas (mm_meas (invM_meas.comp (heisF_meas.comp hX)) (long_weyl_element_measurable.comp hC)) (levM_meas.comp hG))
    (heisF_meas.comp hX')
end Formalism.FourierDecayAlt.P.LongWeylElement
