-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.cwEigen_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:46.130531+00:00
-- url     : https://prove2.me/submissions/547976b5-6e4d-4a62-b60e-da39ffdb7c81

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_diagScalar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchA_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchB_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sum_col_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sum_row_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_QQ_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_cw_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul


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
theorem _root_.solution (hE1 : ExchangePlusFactor) (hE2 : ExchangeMinusFactorStar) (hfixp : XpFix) (hfixm : XmFix) (hT : TTFactor) :
    CwEigen := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w Y hOK hw hreg hY z
  have hA := exchA_mat sites w Y (fun σ hσ => hE1 K A S σ w Y (hOK.1 σ hσ).1 hw) hOK.2
  have hB := exchB_mat sites w Y (fun σ hσ => hE2 K A S σ w Y (hOK.1 σ hσ).1 hw hY) hOK.2
  have hQ := QQ_comm QQ sites w Y (fun σ hσ => (hOK.1 σ hσ).2)
  have hM := cw_mat _ _ _ _ _ _ hA hB hQ
  rw [← hT K A S QQ w Y] at hM
  have hfp := hfixp K A S w Y hw.1 hreg
  have hfm := hfixm K A S w Y hw.1 hreg
  have hCw : (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * TTw QQ w Y * lift0 (sites.map fun σ => Ts σ Y).prod : M2 (SlopeTestRemainingChoices S A)) 0 0 = Cw QQ sites w Y := by
    simp only [Matrix.mul_apply, Finset.sum_mul, lift0, Matrix.map_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    rfl
  have hL : (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * TTw QQ w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod : M2 (SlopeTestRemainingChoices S A)) 0 0 z e1 =
      ∑ z', Cw QQ sites w Y z z' * uw sites w z' := by
    rw [mul_diagScalar_apply, hCw, Matrix.mul_apply]
    rfl
  have hR : ∀ n, ((lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) n 0 = io (∑ k, ∑ l, star ((sites.map fun σ => Ts σ Y).prod k n) * QQ Y k l * (sites.map fun σ => Ts σ Y).prod l 0) := by
    intro n
    simp only [Matrix.mul_apply, Fin.sum_univ_two, lift0, Matrix.map_apply, Matrix.conjTranspose_apply,
      io_add, io_mul, add_mul]
    abel
  have hRow : (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) 0 0 =
      ∑ n, (sites.map fun σ => bT σ w).prod * Xm w Y 0 n * io (∑ k, ∑ l, star ((sites.map fun σ => Ts σ Y).prod k n) * QQ Y k l * (sites.map fun σ => Ts σ Y).prod l 0) := by
    rw [Matrix.mul_apply]
    simp only [diagScalar_mul_apply, hR]
  have hRhs : (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) * Xp w Y : M2 (SlopeTestRemainingChoices S A)) 0 0 z e1 =
      uw sites w z * C0 QQ sites Y := by
    rw [Matrix.mul_apply]
    refine (sum_col_fix (fun m => (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) 0 m)
      (fun m => Xp w Y m 0) z hfp).trans ?_
    show (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) 0 0 z e1 = _
    rw [hRow]
    exact sum_row_fix (sites.map fun σ => bT σ w).prod (fun n => Xm w Y 0 n) (fun n => ∑ k, ∑ l, star ((sites.map fun σ => Ts σ Y).prod k n) * QQ Y k l * (sites.map fun σ => Ts σ Y).prod l 0) z hfm
  exact hL.symm.trans ((congrArg (fun M : M2 (SlopeTestRemainingChoices S A) => M 0 0 z e1) hM).trans hRhs)
end Formalism.FourierDecayAlt.P.Wd8
