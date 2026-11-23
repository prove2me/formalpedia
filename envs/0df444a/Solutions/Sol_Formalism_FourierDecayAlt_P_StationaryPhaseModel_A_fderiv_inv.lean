-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.A_fderiv_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:23.784828+00:00
-- url     : https://prove2.me/submissions/2db4915b-5e7c-4f15-8fa8-c4e1dbcf8acb

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
theorem _root_.solution {f : E → ℝ} (hf : Differentiable ℝ f) (hpos : ∀ x, 0 < f x) :
    fderiv ℝ (fun x => (f x)⁻¹) = fun x => -(((f x)⁻¹ * (f x)⁻¹) • fderiv ℝ f x) := by
  funext x
  have h := (hasDerivAt_inv (hpos x).ne').comp_hasFDerivAt x (hf x).hasFDerivAt
  have h2 : HasFDerivAt (fun x => (f x)⁻¹) ((-(f x ^ 2)⁻¹) • fderiv ℝ f x) x := h
  rw [h2.fderiv, neg_smul, sq, mul_inv]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
