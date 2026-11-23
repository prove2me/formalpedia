-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:34.934373+00:00
-- url     : https://prove2.me/submissions/4f4ad93c-210b-44b3-9d1a-58272d7caa37

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    D_gau d δ = fun x => D_gau d 1 (Real.sqrt δ • x) := by
  funext x
  unfold D_gau
  congr 1
  simp only [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hδ, ← Finset.mul_sum]
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
