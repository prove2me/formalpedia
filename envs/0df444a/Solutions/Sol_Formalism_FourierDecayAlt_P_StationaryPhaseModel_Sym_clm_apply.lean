-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.clm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:12:12.425658+00:00
-- url     : https://prove2.me/submissions/b444bc5b-5b8f-4291-91df-c591cb07b0f7

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
theorem _root_.solution {L : E → G →L[ℝ] F} (v : G) (hL : Sym A w m N K L) :
    Sym A w m N (K * ‖v‖) (fun x => L x v) := by
  refine ⟨hL.1.clm_apply contDiff_const, fun x hx i hi => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i (fun x => L x v) x‖ ≤
      ‖ContinuousLinearMap.apply ℝ F v‖ * ‖iteratedFDeriv ℝ i L x‖ :=
    (ContinuousLinearMap.apply ℝ F v).norm_iteratedFDeriv_comp_left (A_cda hL.1 hi x) le_rfl
  have h2 : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun T => ?_
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact T.le_opNorm v
  calc ‖iteratedFDeriv ℝ i (fun x => L x v) x‖
      ≤ ‖v‖ * ‖iteratedFDeriv ℝ i L x‖ := h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ ≤ ‖v‖ * (K * w x ^ (m - (i : ℤ))) := mul_le_mul_of_nonneg_left (hL.2 x hx i hi) (norm_nonneg v)
    _ = K * ‖v‖ * w x ^ (m - (i : ℤ)) := by ring
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
