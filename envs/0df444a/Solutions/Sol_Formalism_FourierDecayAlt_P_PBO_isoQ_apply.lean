-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBO.isoQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:01.626603+00:00
-- url     : https://prove2.me/submissions/c1b75b92-7bc5-47ba-9ca7-e13e3e68dcc8

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormLeIntegralFsv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBO
namespace Formalism.FourierDecayAlt.P.PBO
theorem _root_.solution (s : ℂ) : isoQ s = conj (Complex.I * s) := rfl
end Formalism.FourierDecayAlt.P.PBO
