-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_iteratedFDeriv_comp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:16.257217+00:00
-- url     : https://prove2.me/submissions/e8f712d5-7926-4e8a-aab6-5d89847dbcfe

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
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f) {i : ℕ} (hi : i ≤ n) (x : E) :
    iteratedFDeriv ℝ i (fun y => f (-y)) x = (-1 : ℝ) ^ i • iteratedFDeriv ℝ i f (-x) := by
  have h := (-(ContinuousLinearMap.id ℝ E)).iteratedFDeriv_comp_right hf x (i := i) (by exact_mod_cast hi)
  have h1 : (f ∘ ⇑(-(ContinuousLinearMap.id ℝ E))) = fun y => f (-y) := by
    funext y; simp
  rw [h1] at h
  rw [h]
  ext v
  have h2 := (iteratedFDeriv ℝ i f (-x)).map_smul_univ (fun _ => (-1 : ℝ)) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply]
  rw [← h2]
  simp
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
