-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.levPP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:51.757816+00:00
-- url     : https://prove2.me/submissions/0149d86d-00a7-4ab5-95bc-7b5e3e7c1d4a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerComm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_mk_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDeriv_commute_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_commute_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDeriv_commute_nabs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_commute_nabs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution : LevPP := by
  intro P l m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact mk_comm _ _ _ _ (eulerComm _ _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact eulerComm _ _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact mk_comm _ _ _ _ (eulerComm _ _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact eulerComm _ _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact mk_comm _ _ _ _ (eulerComm _ _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact eulerComm _ _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact partialDeriv_commute_nab _ _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact partialDerivBar_commute_nab _ _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact partialDeriv_commute_nabs _ _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact partialDerivBar_commute_nabs _ _ _
end Formalism.FourierDecayAlt.P.Mx2
