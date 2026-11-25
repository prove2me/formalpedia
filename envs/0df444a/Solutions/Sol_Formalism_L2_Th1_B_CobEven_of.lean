-- Prove2me | solution 1 for Formalism.L2.Th1.B.CobEven_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:51.773542+00:00
-- url     : https://prove2.me/submissions/10eb0262-d5cb-4e54-b87e-5264d1d82617

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_one_variable
import Theorems.Thm_Formalism_L2_Th1_B_cube_cob_subst
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_inv
import Theorems.Thm_Formalism_L2_Th1_B_cube_add_eq
import Theorems.Thm_Formalism_L2_Th1_B_integral_mvPowerSeries_X
import Theorems.Thm_Formalism_L2_Th1_B_cube_simeq_subst1
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective subst_zero')
namespace Formalism.L2.Th1.B
theorem _root_.solution (hI : SimeqInt) : CobEven := by
  intro K _ _ _ F l i f h hi hq
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  have hs : PowerSeries.HasSubst i := PowerSeries.HasSubst.of_constantCoeff_zero' hi.1
  have comp : ∀ U : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff U = 0 →
      PowerSeries.subst U (PowerSeries.subst i f) = PowerSeries.subst (PowerSeries.subst U i) f :=
    fun U hU => PowerSeries.subst_comp_subst_apply hs (PowerSeries.HasSubst.of_constantCoeff_zero hU) f
  have n0 := constantCoeff_subst_one_variable i hi.1 _ c0
  have n1 := constantCoeff_subst_one_variable i hi.1 _ c1
  have lF : PowerSeries.subst F l = PowerSeries.subst (MvPowerSeries.X 0) l +
      PowerSeries.subst (MvPowerSeries.X 1) l := by
    have e := h.2.2.2.2
    unfold cob at1 at e
    linear_combination e
  have eF : MvPowerSeries.subst ![PowerSeries.subst (MvPowerSeries.X 0) i,
      PowerSeries.subst (MvPowerSeries.X 1) i] F = PowerSeries.subst F i :=
    cube_add_eq h _ _ _ n0 n1 (constantCoeff_subst_one_variable i hi.1 F h.1)
      (by rw [cube_log_inv hi _ c0, cube_log_inv hi _ c1, cube_log_inv hi F h.1, lF]; ring)
  have qF := cube_simeq_subst1 hq F h.1 h.2.1
  have q0 := cube_simeq_subst1 hq _ c0 i0
  have q1 := cube_simeq_subst1 hq _ c1 i1
  rw [comp F h.1] at qF
  rw [comp _ c0] at q0
  rw [comp _ c1] at q1
  have s1 := (hI K (Fin 2) _ _ _ _ qF q0).1
  have s2 := (hI K (Fin 2) _ _ _ _ s1 q1).1
  unfold at1
  rw [cube_cob_subst F h.1 f _ _ n0 n1, eF]
  exact s2
end Formalism.L2.Th1.B
