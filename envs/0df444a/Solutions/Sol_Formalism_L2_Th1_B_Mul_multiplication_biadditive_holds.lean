-- Prove2me | solution 1 for Formalism.L2.Th1.B.Mul.multiplication_biadditive_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:43.100613+00:00
-- url     : https://prove2.me/submissions/0d39262c-d57d-44ae-95db-0079372dec5c

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
import Theorems.Thm_Formalism_L2_Th1_B_Mul_subst_first_coboundary
import Theorems.Thm_Formalism_L2_Th1_B_Mul_simeq_subst3
import Theorems.Thm_Formalism_L2_Th1_B_Mul_formal_multiplication_add
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_integral_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
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
theorem _root_.solution : BiaddMul := by
  intro K _ _ _ F be l h hq n N hN0 hN
  rw [mulN_eq h n N hN0 hN, simeq_iff_cl, cl_int]
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have key := add_rule (fun k : ℤ => cl (MvPowerSeries.subst
      ![at1 0 (mulN h k), (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be))
    (by
      intro a b
      have ca := constantCoeff_series_at_variable (0 : Fin 2) _ (mulN_spec h a).1
      have cb := constantCoeff_series_at_variable (0 : Fin 2) _ (mulN_spec h b).1
      have q := simeq_subst3 hq _ _ _ ca cb c1 (integral_series_at_variable 0 _ (mulN_spec h a).2.1)
        (integral_series_at_variable 0 _ (mulN_spec h b).2.1) (law_integral_X 1)
      rw [subst_first_coboundary F be h.1 _ _ _ ca cb c1, formal_multiplication_add,
        simeq_iff_cl, cl_zero, cl_sub, cl_sub, sub_sub, sub_eq_zero] at q
      exact q) n
  have key' : cl (MvPowerSeries.subst
      ![at1 0 (mulN h n), (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be) =
      n • cl (MvPowerSeries.subst
      ![at1 0 (mulN h 1), (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be) := key
  have e1 : at1 (0 : Fin 2) (PowerSeries.X : PowerSeries K) = MvPowerSeries.X 0 :=
    PowerSeries.subst_X (PowerSeries.HasSubst.X 0)
  rw [key', mulN_one, e1, Formalism.G.LogP.subst_XX]
end Formalism.L2.Th1.B.Mul
