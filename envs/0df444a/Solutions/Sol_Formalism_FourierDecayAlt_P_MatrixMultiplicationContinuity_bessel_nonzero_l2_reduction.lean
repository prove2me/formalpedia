-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.bessel_nonzero_l2_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:46.970025+00:00
-- url     : https://prove2.me/submissions/220691ae-a4c1-46ab-b46d-bc709c5d9ca8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNonvanishingFromL2
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_bessel_nonvanishing_from_L2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := bessel_nonvanishing_from_L2
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
