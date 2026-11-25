-- Prove2me | solution 1 for Formalism.L2.Th1.B.Mul.multiplication_additive_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:08:34.256905+00:00
-- url     : https://prove2.me/submissions/150aea58-16bf-4660-8d46-c49e0a5d41d0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
import Theorems.Thm_Formalism_L2_Th1_B_Mul_add_rule
import Theorems.Thm_Formalism_L2_Th1_B_Mul_simeq_iff_cl
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_sub
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_zero
import Theorems.Thm_Formalism_L2_Th1_B_Mul_cl_int
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_spec
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_eq
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_one
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_add
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_cube_cob_subst
import Theorems.Thm_Formalism_L2_Th1_B_cube_simeq_subst2
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
theorem _root_.solution : AddMul := by
  intro K _ _ _ F l f h hq n N hN0 hN
  rw [mulN_eq h n N hN0 hN, simeq_iff_cl, cl_int]
  have key := add_rule (fun k : ℤ => cl (PowerSeries.subst (mulN h k) f : PowerSeries K))
    (by
      intro a b
      have q := cube_simeq_subst2 hq _ _ (mulN_spec h a).1 (mulN_spec h b).1 (mulN_spec h a).2.1
        (mulN_spec h b).2.1
      rw [cube_cob_subst F h.1 f _ _ (mulN_spec h a).1 (mulN_spec h b).1, mulN_add,
        simeq_iff_cl, cl_zero, cl_sub, cl_sub, sub_sub, sub_eq_zero] at q
      exact q) n
  have key' : cl (PowerSeries.subst (mulN h n) f : PowerSeries K) =
      n • cl (PowerSeries.subst (mulN h 1) f : PowerSeries K) := key
  rw [key', mulN_one, subst_X_self]
end Formalism.L2.Th1.B.Mul
