-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:29.452698+00:00
-- url     : https://prove2.me/submissions/bdc01ee5-1591-49af-beb3-2e87975560df

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_neg

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
theorem _root_.solution {f g : E → F} (hf : Sym A w m N K₁ f) (hg : Sym A w m N K₂ g) :
    Sym A w m N (K₁ + K₂) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
