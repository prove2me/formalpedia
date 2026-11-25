-- Prove2me | solution 1 for Formalism.L2.Th1.B.Mul.multiplication_square_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:37:25.248017+00:00
-- url     : https://prove2.me/submissions/d29f701b-8b92-404e-a220-e56962d7b659

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
import Theorems.Thm_Formalism_L2_Th1_B_Mul_quad_rule
import Theorems.Thm_Formalism_L2_Th1_B_Mul_simeq_iff_cl
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_add
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_sub
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_zero
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_int
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_spec
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_eq
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_zero
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_one
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_add
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_sub
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_eq_zero_of_parallelogram
import Theorems.Thm_Formalism_L2_Th1_B_cube_par_subst
import Theorems.Thm_Formalism_L2_Th1_B_cube_simeq_subst2
import Theorems.Thm_Formalism_L2_Th1_B_law_subst_zero
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Mul
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')
namespace Formalism.L2.Th1.B.Mul
theorem _root_.solution : MulSq := by
  intro K _ _ _ F l i f h hi hq n N hN0 hN
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  rw [mulN_eq h n N hN0 hN, simeq_iff_cl, cl_int]
  have key := quad_rule (fun k : ℤ => cl (PowerSeries.subst (mulN h k) f : PowerSeries K))
    (by
      show cl (PowerSeries.subst (mulN h 0) f : PowerSeries K) = 0
      rw [mulN_zero, law_subst_zero f hf0, cl_zero])
    (by
      intro a b
      have q := cube_simeq_subst2 hq _ _ (mulN_spec h a).1 (mulN_spec h b).1 (mulN_spec h a).2.1
        (mulN_spec h b).2.1
      rw [cube_par_subst F h.1 i f hi.1 _ _ (mulN_spec h a).1 (mulN_spec h b).1, mulN_add,
        mulN_sub h hi, simeq_iff_cl, cl_zero, two_mul, two_mul, cl_sub, cl_sub, cl_add, cl_add,
        cl_add] at q
      show cl (PowerSeries.subst (mulN h (a + b)) f : PowerSeries K) +
        cl (PowerSeries.subst (mulN h (a - b)) f : PowerSeries K) = _
      rw [sub_sub, sub_eq_zero] at q
      rw [q]
      abel) n
  have key' : cl (PowerSeries.subst (mulN h n) f : PowerSeries K) =
      (n ^ 2) • cl (PowerSeries.subst (mulN h 1) f : PowerSeries K) := key
  rw [key', mulN_one, subst_X_self]
end Formalism.L2.Th1.B.Mul
