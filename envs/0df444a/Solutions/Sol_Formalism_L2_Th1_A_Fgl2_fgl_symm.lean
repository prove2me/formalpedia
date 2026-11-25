-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl2.fgl_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:46:20.001391+00:00
-- url     : https://prove2.me/submissions/47b06df1-f48c-451a-ae33-edc856df9594

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_WK
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_univ
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Univ_mv_transfer
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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.Fgl2
theorem _root_.solution : fgl W = (fgl W).subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] := by
  have hK : fgl Univ.WK = (fgl Univ.WK).subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Univ.K₀), MvPowerSeries.X 0] := by
    have hsw : MvPowerSeries.HasSubst
        (![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Univ.K₀), MvPowerSeries.X 0]) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        fin_cases i <;> exact MvPowerSeries.constantCoeff_X _
    have hL : fgl Univ.WK = (expSer Univ.WK).subst
        ((logSer Univ.WK).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Univ.K₀) +
          (logSer Univ.WK).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Univ.K₀)) := by
      have hE := formal_exponential_spec Univ.K₀ Univ.WK
      have hF : PowerSeries.HasSubst (fgl Univ.WK) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (Fgl1.fgl_cc Univ.WK)
      have hLs : PowerSeries.HasSubst (logSer Univ.WK) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (formal_logarithm_spec Univ.K₀ Univ.WK).1
      rw [← log_fgl Univ.WK, ← PowerSeries.subst_comp_subst_apply hLs hF, hE.2.2.2.1, PowerSeries.subst_X hF]
    have hl0 := (Fgl2.formal_logarithm_spec Univ.K₀ Univ.WK).1
    have hc : ∀ a : MvPowerSeries (Fin 2) Univ.K₀, MvPowerSeries.constantCoeff a = 0 →
        MvPowerSeries.constantCoeff ((logSer Univ.WK).subst a) = 0 := fun a ha => by
      rw [PowerSeries.subst, Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun _ => ha)]
      exact hl0
    have hS : MvPowerSeries.constantCoeff ((logSer Univ.WK).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Univ.K₀)
        + (logSer Univ.WK).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Univ.K₀)) = 0 := by
      rw [map_add, hc _ (MvPowerSeries.constantCoeff_X 0), hc _ (MvPowerSeries.constantCoeff_X 1), add_zero]
    conv_rhs => rw [hL]
    rw [mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero hS) hsw, ← MvPowerSeries.coe_substAlgHom hsw,
      map_add, MvPowerSeries.coe_substAlgHom hsw,
      mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)) hsw,
      mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)) hsw,
      MvPowerSeries.subst_X hsw, MvPowerSeries.subst_X hsw]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [add_comm]
    exact hL
  have hZsw : MvPowerSeries.HasSubst
      (![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Univ.Z), MvPowerSeries.X 0]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> exact MvPowerSeries.constantCoeff_X _
  have hι : MvPowerSeries.map Univ.ι (fgl Univ.W₀) = MvPowerSeries.map Univ.ι ((fgl Univ.W₀).subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Univ.Z), MvPowerSeries.X 0]) := by
    rw [MvPowerSeries.map_subst hZsw, cons_map, MvPowerSeries.map_X, MvPowerSeries.map_X, Fgl1.fgl_WK]
    exact hK
  have h := Univ.mv_transfer W hι
  have hRsw : MvPowerSeries.HasSubst
      (![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> exact MvPowerSeries.constantCoeff_X _
  rw [← Fgl1.fgl_univ, MvPowerSeries.map_subst hZsw, cons_map, MvPowerSeries.map_X, MvPowerSeries.map_X,
    ← Fgl1.fgl_univ] at h
  exact h
end Formalism.L2.Th1.A.Fgl2
