-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.exchVecA_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:46.663938+00:00
-- url     : https://prove2.me/submissions/0195b80a-9d31-4ac8-b02a-4a308537de86

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_io_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_diagScalar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exchA_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sum_col_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_io_apply


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
theorem _root_.solution (hE1 : ExchangePlusFactor) (hfix : XpFix) : ExchVecA := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w Y hOK hw hreg k z
  have hM := exchA_mat sites w Y (fun σ hσ => hE1 K A S σ w Y (hOK.1 σ hσ).1 hw) hOK.2
  have hfx := hfix K A S w Y hw.1 hreg
  have hL : (Xp w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod :
      M2 (SlopeTestRemainingChoices S A)) k 0 z e1 =
      ∑ l, ∑ z', (Xp w Y k l : SlopeTestRemainingChoices S A) z z' * (v0 sites Y l * uw sites w z') := by
    rw [mul_diagScalar_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.sum_apply, lift0, Matrix.map_apply, mul_io_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, v0, uw]
  have hR : (d0 (sites.map fun σ => bT σ w).prod * lift0 (sites.map fun σ => Ts σ Y).prod * Xp w Y :
      M2 (SlopeTestRemainingChoices S A)) k 0 z e1 = uw sites w z * v0 sites Y k := by
    rw [Matrix.mul_apply]
    simp only [diagScalar_mul_apply, lift0, Matrix.map_apply]
    rw [sum_col_fix (fun j => (sites.map fun σ => bT σ w).prod * io ((sites.map fun σ => Ts σ Y).prod k j))
      (fun j => Xp w Y j 0) z hfx]
    simp only [mul_io_apply, v0, uw]
  exact hL.symm.trans ((congrArg (fun M : M2 (SlopeTestRemainingChoices S A) => M k 0 z e1) hM).trans hR)
end Formalism.FourierDecayAlt.P.Wd8
