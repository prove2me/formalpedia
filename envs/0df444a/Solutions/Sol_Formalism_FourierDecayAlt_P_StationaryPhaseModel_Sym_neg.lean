-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:26.012024+00:00
-- url     : https://prove2.me/submissions/66ce89e1-f368-4b60-96b6-c494279411fe

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Sym
theorem _root_.solution {f : E → F} (hf : Sym A w m N K f) : Sym A w m N K (fun x => - f x) := by
  refine ⟨hf.1.neg, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => - f x) x = - iteratedFDeriv ℝ i f x :=
    iteratedFDeriv_neg_apply
  rw [h1, norm_neg]
  exact hf.2 x hx i hi
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
