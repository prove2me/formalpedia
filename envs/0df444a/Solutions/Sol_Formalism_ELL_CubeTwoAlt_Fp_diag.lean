-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.Fp_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:05.224959+00:00
-- url     : https://prove2.me/submissions/fcd44136-0309-4f0d-821c-cf03eda47bad

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_w_eq_X_cube_mul_unit
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_wU_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_dI_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_invSer_subst
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_ib_cc
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_inv_formal
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_formalSum
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_formalSum
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_assoc_of
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_ELL_wChordSubst_of
import Theorems.Thm_Formalism_ELL_wSeriesNonsingularPoint_holds
import Theorems.Thm_Formalism_ELL_wSeriesSubstUnique_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {w : PowerSeries K}
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (hw : WFixed W w) :
    ((WeierstrassChordSeries.F2 W w).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]).subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] = 0 := by
  have hU := wSeriesSubstUnique_holds.{u}
  have hS := wChordSubst_of hU
  let FG : FormalGroup K := ⟨WeierstrassChordSeries.F2 W w, constantCoeff_formalSum hw, linearCoeff_formalSum hw 0, linearCoeff_formalSum hw 1,
    WeierstrassCoordinateSubstitution.assoc_of hS wSeriesNonsingularPoint_holds hw (w_eq_X_cube_mul_unit hw) (wU_cc hw) (WeierstrassChordSeries.F2 W w) (constantCoeff_formalSum hw) (linearCoeff_formalSum hw 0)
      (chord hU hw)⟩
  have hdA : dI W w 0 * (dI W w 0)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
  have hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * (-(dI W w 0)⁻¹) = 1 := by
    simp only [dI, Wi] at hdA ⊢; linear_combination hdA
  have key := FormalGroupPointsHom.inv_formal hU hS hw FG (chord hU hw) _ hψ
  have hd : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 (by simp) (by simp)
  rw [MvPowerSeries.subst_comp_subst_apply (FormalGroupPointsHom.hasSubst2 (by simp) (ib_cc hw)) hd]
  have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 0] (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] i)) =
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), -MvPowerSeries.X 0 * -(dI W w 0)⁻¹] := by
    funext i; fin_cases i
    · simp [MvPowerSeries.subst_X hd]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [WeierstrassSubstitution.mvsubst_psubst _ _ (by simp) _ hd, MvPowerSeries.subst_X hd]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [invSer_subst hw 0]; ring
  rw [this]
  exact key
end Formalism.ELL.CubeTwoAlt
