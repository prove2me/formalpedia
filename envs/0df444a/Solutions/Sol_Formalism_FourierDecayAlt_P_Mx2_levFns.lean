-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.levFns
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:32.550785+00:00
-- url     : https://prove2.me/submissions/782bcfa3-3c04-4ea4-a9fa-16f705eeab9d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_gg_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_smul_fnP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_inv1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_inv2

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
theorem _root_.solution : LevFns := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨f, fb, rfl⟩ := form P x hx
    obtain ⟨g, gb, rfl⟩ := form P y hy
    (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact multiplierPair_comm _ _ _ _
  · intro l
    refine ⟨?_, ?_, ?_, ?_⟩
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv1 _ _ (gg_ne _) (gg_ne _)
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact inv2 _ _ (gg_ne _) (gg_ne _)
  · rw [Matrix.algebraMap_eq_diagonal]
    (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π)
    rw [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, ← multiplierPair_one, smul_fnP, zP, zbP, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg,
      multiplierPair_add, ggP]
    congr 1
    · unfold gg; rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    · unfold gg; rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, mul_comm]
end Formalism.FourierDecayAlt.P.Mx2
