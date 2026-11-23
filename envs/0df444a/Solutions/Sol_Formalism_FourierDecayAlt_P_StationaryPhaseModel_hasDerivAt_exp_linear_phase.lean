-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.hasDerivAt_exp_linear_phase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:19.387846+00:00
-- url     : https://prove2.me/submissions/87efdebf-292c-481d-8699-687a9b150f8c

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
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (a p τ s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (((a + s * p) / τ : ℝ) : ℂ)))
      ((Complex.I * ((p / τ : ℝ) : ℂ)) * Complex.exp (Complex.I * (((a + s * p) / τ : ℝ) : ℂ))) s := by
  have h1 : HasDerivAt (fun s : ℝ => (a + s * p) / τ) (p / τ) s := by
    have := ((hasDerivAt_id s).mul_const p).const_add a |>.div_const τ
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => (((a + s * p) / τ : ℝ) : ℂ)) ((p / τ : ℝ) : ℂ) s := h1.ofReal_comp
  have h3 := (h2.const_mul Complex.I).cexp
  convert h3 using 1
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
