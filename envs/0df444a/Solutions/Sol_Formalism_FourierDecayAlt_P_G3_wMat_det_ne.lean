-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.wMat_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:53.667741+00:00
-- url     : https://prove2.me/submissions/1af039bf-75e5-4049-b434-7ae05124d384

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_wMat_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (d : ℕ) : (wMat d).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (wMat_mul_self d)
  simp [Matrix.det_mul, h] at this
end Formalism.FourierDecayAlt.P.G3
