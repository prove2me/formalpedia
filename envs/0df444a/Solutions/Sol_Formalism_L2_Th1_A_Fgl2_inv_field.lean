-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl2.inv_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:20.577863+00:00
-- url     : https://prove2.me/submissions/c2c8f68b-0b92-4838-93a2-9d5e771b8d2d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
import Theorems.Thm_Formalism_L2_Th1_A_Fgl2_formal_logarithm_neg
import Theorems.Thm_Formalism_L2_Th1_A_Fgl2_hasSubst_X_iSer
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl2
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.L2.Th1.A.Fgl2
theorem _root_.solution {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W) = 0 := by
  have hb := hasSubst_X_iSer W
  have hF : PowerSeries.HasSubst (fgl W) := PowerSeries.HasSubst.of_constantCoeff_zero (Fgl1.fgl_cc W)
  have hS := formal_inverse_spec K W
  have hE := formal_exponential_spec K W
  have hN := formal_logarithm_neg K W
  have hself : ∀ f : K⟦X⟧, f.subst (X : K⟦X⟧) = f := fun f => by
    rw [PowerSeries.subst, show (fun _ : Unit => (X : K⟦X⟧)) = MvPowerSeries.X from funext fun _ => rfl,
      MvPowerSeries.subst_self]
    rfl
  have hcG : MvPowerSeries.constantCoeff (MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W)) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun i => by
      fin_cases i
      · exact PowerSeries.constantCoeff_X
      · exact hS.1)]
    exact Fgl1.fgl_cc W
  have hG := PowerSeries.HasSubst.of_constantCoeff_zero hcG
  have hlogG : (logSer W).subst (MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W)) = 0 := by
    have h := congrArg (MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧)) (log_fgl W)
    rw [mvsubst_psubst hF hb, ← MvPowerSeries.coe_substAlgHom hb, map_add, MvPowerSeries.coe_substAlgHom hb,
      mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)) hb,
      mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)) hb,
      MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hself, hN.1, add_neg_cancel] at h
    exact h
  have hsh := PowerSeries.sub_const_eq_X_mul_shift (expSer W)
  simp only [hE.1, map_zero, sub_zero] at hsh
  have h0 : PowerSeries.HasSubst (0 : K⟦X⟧) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  have hT : (expSer W).subst (0 : K⟦X⟧) = 0 := by
    rw [hsh, ← PowerSeries.coe_substAlgHom (R := K) h0, map_mul, PowerSeries.coe_substAlgHom h0,
      PowerSeries.subst_X h0, zero_mul]
  have hL : PowerSeries.HasSubst (logSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (formal_logarithm_spec K W).1
  calc MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W)
      = PowerSeries.subst (MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W)) (X : K⟦X⟧) :=
        (PowerSeries.subst_X hG).symm
    _ = PowerSeries.subst (MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W))
          (PowerSeries.subst (logSer W) (expSer W)) := by
        rw [hE.2.2.2.1]
    _ = PowerSeries.subst (PowerSeries.subst (MvPowerSeries.subst (![X, iSer W] : Fin 2 → K⟦X⟧) (fgl W))
          (logSer W)) (expSer W) :=
        PowerSeries.subst_comp_subst_apply hL hG _
    _ = 0 := by rw [hlogG, hT]
end Formalism.L2.Th1.A.Fgl2
