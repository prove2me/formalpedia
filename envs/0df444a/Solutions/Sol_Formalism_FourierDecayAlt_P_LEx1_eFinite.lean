-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.eFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:09.715642+00:00
-- url     : https://prove2.me/submissions/03c52fe6-424e-4636-ae9b-1b120b0f24bc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : EFinite := by
  intro B S σ ε hε hP hI
  have hc : ContinuousOn (fun Y => S.En ε σ Y / |S.P Y|) S.J :=
    (hI ε hε).2.div (hP.1.abs) (fun Y hY => abs_ne_zero.mpr (hP.2 Y hY))
  exact (isCompact_Icc.image_of_continuousOn hc).bddAbove
end Formalism.FourierDecayAlt.P.LEx1
