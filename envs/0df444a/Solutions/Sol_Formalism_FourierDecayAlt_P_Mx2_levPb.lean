-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.levPb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:40.04186+00:00
-- url     : https://prove2.me/submissions/e4b5310d-e40c-4665-bbcd-fdc185cbdba8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_ec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eci
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vc_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vcb_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vc_vcb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zeta_free_of_variable
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_zi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_zbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_mul_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_pbP_0

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
theorem _root_.solution : LevPb := by
  intro P l
  refine ⟨?_, ?_, ?_⟩
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π)
      rw [cbP, partialDerivBar_mul_fn, ec, ec, if_pos rfl, if_pos rfl]
    · rw [if_neg h, add_zero]; (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π)
      exact pbP_0 _ _ _ (by rw [ec, if_neg (fun e => h ((vcb_inj _ _).1 e))]) (by rw [ec, if_neg (fun e => h ((vc_inj _ _).1 e))])
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π)
      rw [cbiP, partialDerivBar_mul_fn, eci, eci, if_pos rfl, if_pos rfl, sub_eq_add_neg, multiplierPair_neg]
    · rw [if_neg h, sub_zero]; (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π)
      exact pbP_0 _ _ _ (by rw [eci, if_neg (fun e => h ((vcb_inj _ _).1 e))]) (by rw [eci, if_neg (fun e => h ((vc_inj _ _).1 e))])
  · rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (by rw [ec, if_neg (vc_vcb _ _).symm]) (by rw [ec, if_neg (vc_vcb _ _)])
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (by rw [eci, if_neg (vc_vcb _ _).symm]) (by rw [eci, if_neg (vc_vcb _ _)])
    · simp only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (zeta_free_of_variable l).2 (zf_zb l).1
      · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (zf_zi l).2 (zf_zbi l).1
      · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (zf_zb l).2 (zeta_free_of_variable l).1
      · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (zf_zbi l).2 (zf_zi l).1
      · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (zf_gg _ l).2 (zf_gg _ l).1
      · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact pbP_0 _ _ _ (zf_ggi _ l).2 (zf_ggi _ l).1
end Formalism.FourierDecayAlt.P.Mx2
