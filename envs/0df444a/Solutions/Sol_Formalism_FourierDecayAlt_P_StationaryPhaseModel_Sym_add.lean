-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:57.563481+00:00
-- url     : https://prove2.me/submissions/a2632151-6840-4c7f-8df7-7e323aeb6577

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_A_cda

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
    Sym A w m N (K₁ + K₂) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => f x + g x) x = iteratedFDeriv ℝ i f x + iteratedFDeriv ℝ i g x :=
    iteratedFDeriv_add_apply (A_cda hf.1 hi x) (A_cda hg.1 hi x)
  rw [h1, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 x hx i hi) (hg.2 x hx i hi))
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
