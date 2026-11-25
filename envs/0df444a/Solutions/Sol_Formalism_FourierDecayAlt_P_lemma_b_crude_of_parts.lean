-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_b_crude_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:26.507713+00:00
-- url     : https://prove2.me/submissions/16143645-010f-4ce8-bf77-42739adb8d0e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarScaling_AB_le

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.HaarScaling
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.LemmaBCrudeFromParts := by
  intro hC hJ hD hI k r Wp Wq _ _ _ _ _ _ D A hA hF
  exact hC k r Wp Wq D A (AB_le k r A hA) hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)
end Formalism.FourierDecayAlt.P
