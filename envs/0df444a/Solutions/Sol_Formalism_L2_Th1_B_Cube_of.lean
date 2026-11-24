-- Prove2me | solution 1 for Formalism.L2.Th1.B.Cube_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:02.839428+00:00
-- url     : https://prove2.me/submissions/7f9504ed-4388-4470-9d30-5c903c2b8cb4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_one_variable
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_add
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_inv
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_half
import Theorems.Thm_Formalism_L2_Th1_B_cube_identity
import Theorems.Thm_Formalism_L2_Th1_B_parallelogram_coboundary_three_vars
import Theorems.Thm_Formalism_L2_Th1_B_cube_simeq_congr
import Theorems.Thm_Formalism_L2_Th1_B_integral_mvPowerSeries_X
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_eq_zero_of_parallelogram
import Theorems.Thm_Formalism_L2_Th1_B_integral_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_integral_subst_one_variable
import Theorems.Thm_Formalism_L2_Th1_B_cube_simeq_subst2
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
theorem _root_.solution (hH : HalfExists) (hI : SimeqInt) : Cube := by
  intro K _ _ _ F l i f h hi h2 hq
  obtain ⟨hf, hh⟩ := hH K F l h h2
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 3)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 3)
  have i2 := integral_mvPowerSeries_X (K := K) (2 : Fin 3)

  obtain ⟨S, hS⟩ : ∃ S, S = MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K),
    PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) i] F := ⟨_, rfl⟩
  have cN := constantCoeff_subst_one_variable i hi.1 _ c2
  have iN := integral_subst_one_variable hi.2.1 _ c2 i2
  have cS : MvPowerSeries.constantCoeff S = 0 := hS ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 c2
  have cD : MvPowerSeries.constantCoeff D = 0 := hD ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 cN
  have iS : Integral S := hS ▸ integral_subst_two_variables h.2.1 _ _ c1 c2 i1 i2
  have iD : Integral D := hD ▸ integral_subst_two_variables h.2.1 _ _ c1 cN i1 iN
  have lS : PowerSeries.subst S l = PowerSeries.subst (MvPowerSeries.X 1) l +
      PowerSeries.subst (MvPowerSeries.X 2) l := hS ▸ cube_log_add h _ _ c1 c2
  have lD : PowerSeries.subst D l = PowerSeries.subst (MvPowerSeries.X 1) l -
      PowerSeries.subst (MvPowerSeries.X 2) l := by
    rw [hD, cube_log_add h _ _ c1 cN, cube_log_inv hi _ c2]; ring
  have cB := constantCoeff_subst_one_variable hf hh.1 S cS
  have cC := constantCoeff_subst_one_variable hf hh.1 D cD
  have iB := integral_subst_one_variable hh.2.1 S cS iS
  have iC := integral_subst_one_variable hh.2.1 D cD iD
  have cA := constantCoeff_subst_two_variables F h.1 _ _ c0 cB
  have iA := integral_subst_two_variables h.2.1 _ _ c0 cB i0 iB
  have key := cube_identity h hi f hf0 (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    _ _ _ c0 c1 c2 cA cB cC (cube_log_add h _ _ c0 cB)
    ((cube_log_half hh S cS).trans lS) ((cube_log_half hh D cD).trans lD)
  rw [parallelogram_coboundary_three_vars F h.1 f, ← key]
  have qAB := cube_simeq_subst2 hq _ _ cA cB iA iB
  have qAC := cube_simeq_subst2 hq _ _ cA cC iA iC
  have qBC := cube_simeq_subst2 hq _ _ cB cC iB iC
  have qBB := cube_simeq_subst2 hq _ _ cB cB iB iB
  have s1 := (hI K (Fin 3) _ _ _ _ qAB qAC).1
  have s2 := (equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 qBC
  have s3 := (hI K (Fin 3) _ _ _ _ s2 qBB).1
  exact cube_simeq_congr (by ring) s3
end Formalism.L2.Th1.B
