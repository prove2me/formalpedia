-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.norm_det_wMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:34.581891+00:00
-- url     : https://prove2.me/submissions/75896329-c3f6-4a08-836f-9f6d8d935f21

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_wMat_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (n : ℕ) : ‖(wMat n).det‖ = 1 := by
  have h := congrArg Matrix.det (G3.wMat_mul_self n)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have h2 : ‖(wMat n).det‖ * ‖(wMat n).det‖ = 1 := by rw [← norm_mul, h, norm_one]
  nlinarith [norm_nonneg (wMat n).det]
end Formalism.FourierDecayAlt.P.G7
