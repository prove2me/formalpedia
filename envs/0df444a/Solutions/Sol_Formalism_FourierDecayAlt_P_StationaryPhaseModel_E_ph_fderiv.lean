-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:45.691029+00:00
-- url     : https://prove2.me/submissions/19d7c655-b5fb-4bf3-9b6d-64a1f9a9f165

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_hasFDerivAt

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
theorem _root_.solution {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (s : ℝ) :
    fderiv ℝ (fun y => quad φ y + s * E_P φ y) =
      fun x => (1 - s) • (fderiv ℝ (fderiv ℝ φ) 0 x) + s • fderiv ℝ φ x := by
  funext x
  have hP : HasFDerivAt (E_P φ) (fderiv ℝ φ x - fderiv ℝ (fderiv ℝ φ) 0 x) x :=
    ((hφ.differentiable (by norm_num)) x).hasFDerivAt.sub (E_quad_hasFDerivAt hφ x)
  have h : HasFDerivAt (fun y => quad φ y + s * E_P φ y)
      (fderiv ℝ (fderiv ℝ φ) 0 x + s • (fderiv ℝ φ x - fderiv ℝ (fderiv ℝ φ) 0 x)) x :=
    (E_quad_hasFDerivAt hφ x).add (hP.const_mul s)
  rw [h.fderiv]
  module
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
