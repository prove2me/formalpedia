-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_quad_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:30.381974+00:00
-- url     : https://prove2.me/submissions/d1bdf0b3-0f3a-4f2e-8c20-eb00390340d9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    HasFDerivAt (quad φ) (fderiv ℝ (fderiv ℝ φ) 0 x) x := by
  have h := (fderiv ℝ (fderiv ℝ φ) 0).hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  have h2 := (h.const_mul (1 / 2 : ℝ)).const_add (φ 0)
  refine h2.congr_fderiv ?_
  ext v
  simp [E_symm hφ v x]
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
