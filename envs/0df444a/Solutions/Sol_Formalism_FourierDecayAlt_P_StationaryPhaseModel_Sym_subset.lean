-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:35.455541+00:00
-- url     : https://prove2.me/submissions/24ba8cca-b4d6-4bfc-9141-9cf67b2671f0

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
theorem _root_.solution {f : E → F} {A' : Set E} (h : Sym A w m N K f) (hA : A' ⊆ A) : Sym A' w m N K f :=
  ⟨h.1, fun x hx i hi => h.2 x (hA hx) i hi⟩
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
