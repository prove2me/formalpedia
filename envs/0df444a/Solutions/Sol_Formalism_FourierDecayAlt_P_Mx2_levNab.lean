-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.levNab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:38.90834+00:00
-- url     : https://prove2.me/submissions/8d8cc8f2-60ab-45ce-b7ab-60881e7791b7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vz_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabla_zeta_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_zi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eci
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_cf_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_cf_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_cf_ci
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_cf_cbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nab_cf

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
theorem _root_.solution : LevNab := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nabla_zeta_comm _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_zi _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_zb _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_cf _ _ _ _ (by rw [eci, if_neg vz_ne]) (by rw [eci, if_neg vz_ne.symm])
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_gg _ _
  · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_ggi _ _
  · rintro x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_cf _ _ _ _ (cf_c m).1 (cf_cb m).2
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_cf _ _ _ _ (cf_ci m).1 (cf_cbi m).2
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_cf _ _ _ _ (cf_cb m).1 (cf_c m).2
    · (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π); exact nab_cf _ _ _ _ (cf_cbi m).1 (cf_ci m).2
end Formalism.FourierDecayAlt.P.Mx2
