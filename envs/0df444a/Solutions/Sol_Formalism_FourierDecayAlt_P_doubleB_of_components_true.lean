-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.doubleB_of_components_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:53.621364+00:00
-- url     : https://prove2.me/submissions/4edf22f7-4521-4225-a089-3d08b8cae05e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_BesselScaling_AB_pos

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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.LemmaBDoubleFromParts := by
  intro hC hJ hD hI hX k r Wp Wq _ _ _ _ _ _ D A hA hF
  have hAB : AB k r ≤ A := by
    have := Formalism.FourierDecayAlt.P.BesselScaling.AB_pos k r
    linarith
  exact hC hX k r Wp Wq D A hAB hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI hX k r Wp Wq D A hA)
end Formalism.FourierDecayAlt.P
