-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_sym_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:54.908977+00:00
-- url     : https://prove2.me/submissions/83376d5b-eadd-4d99-823a-cac30ada1bcb

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {A : Set E} {w : E → ℝ} {m : ℤ} {N : ℕ} {K : ℝ} {f : E → F} (hf : Sym A w m N K f)
    (hs : tsupport f ⊆ A) (hK : 0 ≤ K) (hw : ∀ x, 0 < w x) : Sym Set.univ w m N K f := by
  refine ⟨hf.1, fun x _ i hi => ?_⟩
  by_cases hx : x ∈ A
  · exact hf.2 x hx i hi
  · have h1 : x ∉ tsupport (iteratedFDeriv ℝ i f) := fun h => hx (hs (tsupport_iteratedFDeriv_subset i h))
    rw [image_eq_zero_of_notMem_tsupport h1, norm_zero]
    exact mul_nonneg hK (zpow_nonneg (hw x).le _)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
