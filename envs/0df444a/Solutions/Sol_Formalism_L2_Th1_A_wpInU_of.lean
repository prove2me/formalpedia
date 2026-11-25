-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpInU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:08:19.374748+00:00
-- url     : https://prove2.me/submissions/a068e38e-5368-4e37-b329-f624d0689d51

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_wpInZ
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
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
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Two
namespace Formalism.L2.Th1.A
theorem _root_.solution (hS : WpShape.{u}) : WpInU.{u} := by
  intro K _ _ W
  have h := Two.wpInZ W hS
  have hl : PowerSeries.HasSubst (logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' (logSpec K W).1
  have hel : (expSer W).subst (logSer W) = X := (expSpec K W).2.2.2.1
  have hself : ∀ f : K⟦X⟧, f.subst (X : K⟦X⟧) = f := fun f => by
    show MvPowerSeries.subst (fun _ => (PowerSeries.X : K⟦X⟧)) f = f
    have e : (fun _ : Unit => (PowerSeries.X : K⟦X⟧)) = MvPowerSeries.X := funext fun _ => rfl
    rw [e, MvPowerSeries.subst_self]
    rfl
  have h2 := congrArg (PowerSeries.substAlgHom hl) h
  simp only [map_mul, map_pow, map_add, map_one, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hl] at h2
  have e1 : PowerSeries.substAlgHom hl (expSer W) = X := by rw [PowerSeries.coe_substAlgHom]; exact hel
  have e2 : PowerSeries.substAlgHom hl (wpReg W) = (wpReg W).subst (logSer W) := by
    rw [PowerSeries.coe_substAlgHom]
  have e3 : PowerSeries.substAlgHom hl ((xS W).subst (expSer W)) = xS W := by
    rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_comp_subst_apply (Two.he W) hl, hel, hself]
  have e4 : PowerSeries.substAlgHom hl (C (W.b₂ / 12)) = C (W.b₂ / 12) :=
    (PowerSeries.substAlgHom hl).commutes _
  have e3' : PowerSeries.subst (logSer W : K⟦X⟧) (PowerSeries.subst (expSer W : K⟦X⟧) (xS W)) = xS W := by
    rw [PowerSeries.subst_comp_subst_apply (Two.he W) hl, hel, hself]
  have e4' : PowerSeries.subst (logSer W : K⟦X⟧) (C (W.b₂ / 12) : K⟦X⟧) = C (W.b₂ / 12) := by
    rw [← PowerSeries.coe_substAlgHom hl]
    exact (PowerSeries.substAlgHom hl).commutes _
  simp only [e1, e2, e3, e4, hel, e3', e4'] at h2
  exact h2
end Formalism.L2.Th1.A
