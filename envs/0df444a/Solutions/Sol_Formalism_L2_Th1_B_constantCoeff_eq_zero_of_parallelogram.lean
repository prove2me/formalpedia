-- Prove2me | solution 1 for Formalism.L2.Th1.B.constantCoeff_eq_zero_of_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:01.445348+00:00
-- url     : https://prove2.me/submissions/f767c98b-920a-4369-b2fe-20030b68d771

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_cube_par_subst
import Theorems.Thm_Formalism_L2_Th1_B_cube_add_eq
import Theorems.Thm_Formalism_L2_Th1_B_cube_sub_eq
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l i f : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (hq : Simeq (par F i f) 0) : PowerSeries.constantCoeff f = 0 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have e := Formalism.G.LogP.constantCoeff_subst_of_zero (par F i f)
    (b := ![(0 : MvPowerSeries (Fin 2) K), 0]) (fun j => by fin_cases j <;> simp)
  have hq0 : MvPowerSeries.constantCoeff (par F i f) = 0 := by simpa using hq.1
  have lz : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  rw [hq0, cube_par_subst F h.1 i f hi.1 0 0 h0 h0,
    cube_add_eq h 0 0 0 h0 h0 h0 (by rw [lz]; ring),
    cube_sub_eq h hi 0 0 0 h0 h0 h0 (by rw [lz]; ring),
    PowerSeries.subst_zero_eq_C_constantCoeff] at e
  have e' : PowerSeries.constantCoeff f + PowerSeries.constantCoeff f -
      2 * PowerSeries.constantCoeff f - 2 * PowerSeries.constantCoeff f = 0 := by
    have c2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries (Fin 2) K) = 2 :=
      map_ofNat MvPowerSeries.constantCoeff 2
    simpa [c2] using e
  have e2 : (2 : K) * PowerSeries.constantCoeff f = 0 := by linear_combination -e'
  exact (mul_eq_zero.1 e2).resolve_left two_ne_zero
end Formalism.L2.Th1.B
