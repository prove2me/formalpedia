-- Prove2me | solution 1 for Formalism.L2.Th1.A.bridgeCurve_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:22.956371+00:00
-- url     : https://prove2.me/submissions/5bc395ca-1f22-433b-a85d-f87f6a164344

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
import Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_of_coeff
import Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_map
import Theorems.Thm_Formalism_L2_Th1_A_Bridge_model_map
import Theorems.Thm_Formalism_ELL_EulerSeries_integral_map
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_map
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_iSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_xS
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_xS_cc
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_fglMap
import Theorems.Thm_Formalism_L2_Th1_A_iSerSpec
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
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Bridge
namespace Formalism.L2.Th1.A
theorem _root_.solution (hM : CoeffMem.{0}) (hU : WpInU.{0}) (hC : CubeTwoR.{0}) :
    BridgeCurve := by
  intro K _ _ _ W hW
  obtain ⟨-, hx, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  refine ⟨integral_of_coeff hx, CurveSer.xS_cc W, hU K W, ?_⟩
  obtain ⟨c, hc0, hc⟩ := hC (Formalism.G.unitBall K) (model W hW)
  refine ⟨MvPowerSeries.map (Formalism.G.unitBall K).subtype c, integral_map c, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hc0]
    simp
  · have hi0 : constantCoeff (iSer (model W hW)) = 0 := (iSerSpec _ (model W hW)).1
    have hs : MvPowerSeries.HasSubst
        (![U₁, (iSer (model W hW)).subst
            (U₂ : MvPowerSeries (Fin 2) (Formalism.G.unitBall K))] :
          Fin 2 → MvPowerSeries (Fin 2) (Formalism.G.unitBall K)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      fin_cases i
      · simp
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) _ hi0
    have key := congrArg (MvPowerSeries.map (Formalism.G.unitBall K).subtype) hc
    rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, MvPowerSeries.map_X,
      MvPowerSeries.map_X, PowerSeries.map_subst (HasSubst.X 0),
      PowerSeries.map_subst (HasSubst.X 1), MvPowerSeries.map_X, MvPowerSeries.map_X,
      CurveSer.map_xS, MvPowerSeries.map_subst hs, fglMap, model_map] at key
    unfold Formalism.L2.Th1.B.FI Formalism.InvariantFactorPaths.G7.at1
    rw [key]
    congr 2
    funext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [PowerSeries.map_subst (HasSubst.X 1), MvPowerSeries.map_X, CurveSer.map_iSer, model_map]
end Formalism.L2.Th1.A
