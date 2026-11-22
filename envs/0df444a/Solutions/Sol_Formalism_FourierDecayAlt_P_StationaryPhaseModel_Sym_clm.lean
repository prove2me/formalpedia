-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:21.053359+00:00
-- url     : https://prove2.me/submissions/04679859-3af9-43d9-9ce1-8d6821e42267

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
theorem _root_.solution (L : E →L[ℝ] F) {σ : ℝ} (hσ : 0 < σ) : Sym A (wt σ) 1 N ‖L‖ (fun x => L x) := by
  refine ⟨L.contDiff, fun x _ i _ => ?_⟩
  have hwpos : 0 < wt σ x := by unfold wt; positivity
  match i with
  | 0 =>
    rw [norm_iteratedFDeriv_zero]
    have : wt σ x ^ ((1 : ℤ) - ((0 : ℕ) : ℤ)) = wt σ x := by simp
    rw [this]
    refine (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
    unfold wt
    linarith
  | 1 =>
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
    have h1 : _root_.fderiv ℝ (fun x => L x) x = L := L.fderiv
    rw [h1]
    simp
  | j + 2 =>
    rw [← norm_iteratedFDeriv_fderiv]
    have h1 : _root_.fderiv ℝ (fun x => L x) = fun _ => L := by
      funext y
      exact L.fderiv
    rw [h1, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simpa using mul_nonneg (norm_nonneg L) (zpow_pos hwpos _).le
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
