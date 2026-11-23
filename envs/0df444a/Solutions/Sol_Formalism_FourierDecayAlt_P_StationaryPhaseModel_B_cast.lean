-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:26.490552+00:00
-- url     : https://prove2.me/submissions/e9534af0-6a24-4fe5-8e78-d4b80c259c4d

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
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Set E} {w : E → ℝ} {m m' : ℤ} {N : ℕ}
    {K K' : ℝ} {f : E → F} (h : Sym A w m N K f) (hm : m = m') (hK : K = K') : Sym A w m' N K' f := by
  subst hm; subst hK; exact h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
