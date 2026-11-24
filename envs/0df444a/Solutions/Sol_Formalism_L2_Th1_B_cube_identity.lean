-- Prove2me | solution 1 for Formalism.L2.Th1.B.cube_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:58.65805+00:00
-- url     : https://prove2.me/submissions/2261a489-d9ec-48a5-8b09-4c091e228ecc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_cube_par_subst
import Theorems.Thm_Formalism_L2_Th1_B_two_mul_C_inv_two
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_add
import Theorems.Thm_Formalism_L2_Th1_B_cube_add_eq
import Theorems.Thm_Formalism_L2_Th1_B_cube_sub_eq
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
variable {K : Type} [NormedField K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (f : PowerSeries K) (hf0 : PowerSeries.constantCoeff f = 0)
    (x0 x1 x2 A B C : MvPowerSeries ι K)
    (h0 : MvPowerSeries.constantCoeff x0 = 0) (h1 : MvPowerSeries.constantCoeff x1 = 0)
    (h2 : MvPowerSeries.constantCoeff x2 = 0) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hC : MvPowerSeries.constantCoeff C = 0)
    (eA : PowerSeries.subst A l = PowerSeries.subst x0 l + PowerSeries.subst B l)
    (eB : 2 * PowerSeries.subst B l = PowerSeries.subst x1 l + PowerSeries.subst x2 l)
    (eC : 2 * PowerSeries.subst C l = PowerSeries.subst x1 l - PowerSeries.subst x2 l) :
    MvPowerSeries.subst ![A, B] (par F i f) - MvPowerSeries.subst ![A, C] (par F i f) +
        MvPowerSeries.subst ![B, C] (par F i f) - MvPowerSeries.subst ![B, B] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x1] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x1, x2] F) f +
        PowerSeries.subst x0 f + PowerSeries.subst x1 f + PowerSeries.subst x2 f := by
  have c01 := constantCoeff_subst_two_variables F h.1 x0 x1 h0 h1
  have c02 := constantCoeff_subst_two_variables F h.1 x0 x2 h0 h2
  have c12 := constantCoeff_subst_two_variables F h.1 x1 x2 h1 h2
  have c012 := constantCoeff_subst_two_variables F h.1 _ x2 c01 h2
  have l01 := cube_log_add h x0 x1 h0 h1
  have l02 := cube_log_add h x0 x2 h0 h2
  have l12 := cube_log_add h x1 x2 h1 h2
  have l012 := cube_log_add h _ x2 c01 h2
  have lz : PowerSeries.subst (0 : MvPowerSeries ι K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  have fz : PowerSeries.subst (0 : MvPowerSeries ι K) f = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero hf0
  have e1 : MvPowerSeries.subst ![A, B] F =
      MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F :=
    cube_add_eq h A B _ hA hB c012 (by rw [l012, l01]; linear_combination eA + eB)
  have e2 : MvPowerSeries.subst ![A, PowerSeries.subst B i] F = x0 :=
    cube_sub_eq h hi A B _ hA hB h0 (by linear_combination eA)
  have hc := two_mul_C_inv_two (K := K) (ι := ι)
  have sBC : PowerSeries.subst B l + PowerSeries.subst C l = PowerSeries.subst x1 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB + (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l + PowerSeries.subst C l - PowerSeries.subst x1 l) * hc
  have dBC : PowerSeries.subst B l - PowerSeries.subst C l = PowerSeries.subst x2 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB - (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l - PowerSeries.subst C l - PowerSeries.subst x2 l) * hc
  have e3 : MvPowerSeries.subst ![A, C] F = MvPowerSeries.subst ![x0, x1] F :=
    cube_add_eq h A C _ hA hC c01 (by rw [l01]; linear_combination eA + sBC)
  have e4 : MvPowerSeries.subst ![A, PowerSeries.subst C i] F = MvPowerSeries.subst ![x0, x2] F :=
    cube_sub_eq h hi A C _ hA hC c02 (by rw [l02]; linear_combination eA + dBC)
  have e5 : MvPowerSeries.subst ![B, C] F = x1 := cube_add_eq h B C _ hB hC h1 sBC
  have e6 : MvPowerSeries.subst ![B, PowerSeries.subst C i] F = x2 :=
    cube_sub_eq h hi B C _ hB hC h2 dBC
  have e7 : MvPowerSeries.subst ![B, B] F = MvPowerSeries.subst ![x1, x2] F :=
    cube_add_eq h B B _ hB hB c12 (by rw [l12]; linear_combination eB)
  have e8 : MvPowerSeries.subst ![B, PowerSeries.subst B i] F = 0 :=
    cube_sub_eq h hi B B _ hB hB (by simp) (by rw [lz]; ring)
  rw [cube_par_subst F h.1 i f hi.1 A B hA hB, cube_par_subst F h.1 i f hi.1 A C hA hC,
    cube_par_subst F h.1 i f hi.1 B C hB hC, cube_par_subst F h.1 i f hi.1 B B hB hB,
    e1, e2, e3, e4, e5, e6, e7, e8, fz]
  ring
end Formalism.L2.Th1.B
