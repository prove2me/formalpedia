-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_hasFDerivAt_osc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:24.436823+00:00
-- url     : https://prove2.me/submissions/a037f710-4201-42c3-9e71-5bfbca51fa45

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

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
theorem _root_.solution {φ : E → ℝ} (τ : ℝ) {x : E} (hφ : DifferentiableAt ℝ φ x) :
    HasFDerivAt (osc φ τ)
      ((Complex.I * osc φ τ x) • (Complex.ofRealCLM.comp (τ⁻¹ • fderiv ℝ φ x))) x := by
  unfold osc
  have h1 : HasFDerivAt (fun y => ((φ y / τ : ℝ) : ℂ)) (Complex.ofRealCLM.comp (τ⁻¹ • fderiv ℝ φ x)) x := by
    have h2 : HasFDerivAt (fun y => φ y / τ) (τ⁻¹ • fderiv ℝ φ x) x := by
      simpa [div_eq_inv_mul] using hφ.hasFDerivAt.const_mul τ⁻¹
    exact Complex.ofRealCLM.hasFDerivAt.comp x h2
  have h3 := (h1.const_mul Complex.I).cexp
  convert h3 using 1
  rw [smul_smul, mul_comm Complex.I]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
