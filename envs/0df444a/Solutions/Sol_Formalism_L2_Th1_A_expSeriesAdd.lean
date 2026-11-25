-- Prove2me | solution 1 for Formalism.L2.Th1.A.expSeriesAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:14.769371+00:00
-- url     : https://prove2.me/submissions/ce7b3a1f-b26c-4a64-a2f3-88f7108033d3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_fglLog
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Nn
namespace Formalism.L2.Th1.A
theorem _root_.solution : ExpAdd.{u} := by
  intro K _ _ W
  obtain ⟨l0, -, -, -⟩ := logSpec K W
  obtain ⟨e0, -, hle, -, -⟩ := expSpec K W
  have c0 : MvPowerSeries.constantCoeff (U₁ : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (U₂ : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hU0 : HasSubst (U₁ : MvPowerSeries (Fin 2) K) := HasSubst.of_constantCoeff_zero c0
  have hU1 : HasSubst (U₂ : MvPowerSeries (Fin 2) K) := HasSubst.of_constantCoeff_zero c1
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  have ce0 : MvPowerSeries.constantCoeff ((expSer W).subst (U₁ : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero c0 _ e0
  have ce1 : MvPowerSeries.constantCoeff ((expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero c1 _ e0
  have hb : MvPowerSeries.HasSubst (![(expSer W).subst (U₁ : MvPowerSeries (Fin 2) K),
      (expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s
      · exact ce0
      · exact ce1)
  have cl : MvPowerSeries.constantCoeff ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero c0 _ l0,
      PowerSeries.constantCoeff_subst_eq_zero c1 _ l0, add_zero]
  have k0 : (logSer W).subst ((expSer W).subst (U₁ : MvPowerSeries (Fin 2) K)) = U₁ := by
    have key := subst_comp_subst_apply he hU0 (logSer W)
    rw [hle, subst_X hU0] at key
    exact key.symm
  have k1 : (logSer W).subst ((expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)) = U₂ := by
    have key := subst_comp_subst_apply he hU1 (logSer W)
    rw [hle, subst_X hU1] at key
    exact key.symm
  conv_rhs => rw [(fglLog K W).2]
  rw [Fgl2.mvsubst_psubst (HasSubst.of_constantCoeff_zero cl) hb, MvPowerSeries.subst_add hb,
    Fgl2.mvsubst_psubst hU0 hb, Fgl2.mvsubst_psubst hU1 hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [k0, k1]
end Formalism.L2.Th1.A
