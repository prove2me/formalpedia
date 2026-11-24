-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.exchVecB_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:22.727395+00:00
-- url     : https://prove2.me/submissions/8ca75c71-98d4-4bc9-a51b-05543a1ef903

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_diagScalar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchB_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sum_row_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (hE2 : ExchangeMinusFactorStar) (hfix : XmFix) : ExchVecB := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w Y hOK hw hreg hY l z
  have hM := exchB_mat sites w Y (fun σ hσ => hE2 K A S σ w Y (hOK.1 σ hσ).1 hw hY) hOK.2
  have hfx := hfix K A S w Y hw.1 hreg
  have hL : (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * Xm w Y * d0 (sites.map fun σ => bT σ w).prod :
      M2 (SlopeTestRemainingChoices S A)) 0 l z e1 =
      ∑ k, ∑ z', star (v0 sites Y k) * (Xm w Y k l : SlopeTestRemainingChoices S A) z z' * uw sites w z' := by
    rw [mul_diagScalar_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.sum_apply, lift0, Matrix.map_apply, Matrix.conjTranspose_apply, io_mul_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [v0, uw]
  have hR : (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ :
      M2 (SlopeTestRemainingChoices S A)) 0 l z e1 = uw sites w z * star (v0 sites Y l) := by
    rw [Matrix.mul_apply]
    simp only [diagScalar_mul_apply, lift0, Matrix.map_apply, Matrix.conjTranspose_apply]
    rw [sum_row_fix _ (fun j => Xm w Y 0 j) (fun j => star ((sites.map fun σ => Ts σ Y).prod l j)) z hfx]
    simp only [v0, uw]
  exact hL.symm.trans ((congrArg (fun M : M2 (SlopeTestRemainingChoices S A) => M 0 l z e1) hM).trans hR)
end Formalism.FourierDecayAlt.P.Wd8
