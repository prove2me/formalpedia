-- Prove2me | solution 1 for Formalism.L2.Th1.B.diagonal_two_variable_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:48:01.403245+00:00
-- url     : https://prove2.me/submissions/a16db762-9455-4361-9fbe-c463593b4c45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_cube_cob_subst
import Theorems.Thm_Formalism_L2_Th1_B_cube_par_subst
import Theorems.Thm_Formalism_L2_Th1_B_cube_sub_eq
import Theorems.Thm_Formalism_L2_Th1_B_cube_simeq_congr
import Theorems.Thm_Formalism_L2_Th1_B_integral_mvPowerSeries_X
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_eq_zero_of_parallelogram
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
theorem _root_.solution : DiagTwo := by
  intro K _ _ _ F l i f h hi hq
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  have cX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
    PowerSeries.constantCoeff_X
  have iX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := integral_mvPowerSeries_X ()
  have fX : PowerSeries.subst (PowerSeries.X : PowerSeries K) f = f := by
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp
  have lz : PowerSeries.subst (0 : PowerSeries K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  have fz : PowerSeries.subst (0 : PowerSeries K) f = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero hf0
  have q := cube_simeq_subst2 hq _ _ cX cX iX iX
  rw [cube_par_subst F h.1 i f hi.1 _ _ cX cX,
    cube_sub_eq h hi _ _ 0 cX cX (by simp) (by rw [lz]; ring), fz, fX] at q
  refine ⟨cube_simeq_congr (by ring) q, ?_⟩
  rw [cube_cob_subst F h.1 f _ _ cX cX, fX]
  exact cube_simeq_congr (by ring) q
end Formalism.L2.Th1.B
