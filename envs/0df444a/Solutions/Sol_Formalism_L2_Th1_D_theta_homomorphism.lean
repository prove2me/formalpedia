-- Prove2me | solution 1 for Formalism.L2.Th1.D.theta_homomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:13.935152+00:00
-- url     : https://prove2.me/submissions/14c13ae6-bee5-4cf9-984a-26b3a911a30e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_L2_Th1_D_EAux_cc_a
import Theorems.Thm_Formalism_L2_Th1_D_EAux_thetaS_eq
import Theorems.Thm_Formalism_L2_Th1_D_EAux_cc_theta
import Theorems.Thm_Formalism_L2_Th1_D_EAux_log_theta
import Theorems.Thm_Formalism_L2_Th1_D_EAux_subst_C_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_two_le
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_fglLog
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
import Theorems.Thm_Formalism_L2_Th1_B_Add1_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_ps
import Theorems.Thm_Formalism_L2_Th1_D_Pair_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_expSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)
open Formalism.L2.Th1.A (shortW logSer expSer fgl wpReg iSer xS IntModel)
open Formalism.L2.Th1.B (fLog lU sigS phO)
open EAux
namespace Formalism.L2.Th1.D
theorem _root_.solution : ThetaHom := by
  intro K _ _ _ l hl _ F hF g2 g3 ε
  have h2 : 2 ≤ l := hl.two_le
  obtain ⟨hF0, -, hFc⟩ := hF
  have hE := Formalism.L2.Th1.A.expSpec K (shortW g2 g3)
  have hθ0 := cc_theta h2 g2 g3 ε
  have ha := cc_a h2 ε
  refine ⟨log_theta h2 g2 g3 ε, hθ0, ?_⟩
  have hlog : ∀ x : Fin 2, PowerSeries.subst (at1 x (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) =
      MvPowerSeries.C ε * at1 x (lgF K l) := by
    intro x
    unfold at1
    rw [Pair.ps_comp (by simp) hθ0, log_theta h2, subst_C_mul (by simp)]
  have hs := Pair.hs2 (Pair.constantCoeff_inVar_eq_zero (0 : Fin 2) hθ0) (Pair.constantCoeff_inVar_eq_zero (1 : Fin 2) hθ0)
  have hL0 := (Formalism.L2.Th1.A.logSpec K (shortW g2 g3)).1
  have hsum : MvPowerSeries.constantCoeff
      (PowerSeries.subst (Formalism.L2.Th1.A.U₁ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3)) +
        PowerSeries.subst (Formalism.L2.Th1.A.U₂ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) = 0 := by
    rw [map_add, Pair.cc_ps (by simp) hL0, Pair.cc_ps (by simp) hL0, add_zero]
  have hFl : PowerSeries.subst F (lgF K l) = at1 0 (lgF K l) + at1 1 (lgF K l) := by
    unfold cob at hFc
    rw [sub_sub, sub_eq_zero] at hFc
    exact hFc
  conv_rhs => rw [(Formalism.L2.Th1.A.fglLog K (shortW g2 g3)).2]
  rw [Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hsum),
    MvPowerSeries.subst_add hs]
  have e0 : MvPowerSeries.subst ![at1 (0 : Fin 2) (thetaS l g2 g3 ε), at1 (1 : Fin 2) (thetaS l g2 g3 ε)]
      (PowerSeries.subst (Formalism.L2.Th1.A.U₁ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) =
      PowerSeries.subst (at1 0 (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) :=
    Pair.subst_single_var hs (0 : Fin 2) (logSer (shortW g2 g3))
  have e1 : MvPowerSeries.subst ![at1 (0 : Fin 2) (thetaS l g2 g3 ε), at1 (1 : Fin 2) (thetaS l g2 g3 ε)]
      (PowerSeries.subst (Formalism.L2.Th1.A.U₂ : MvPowerSeries (Fin 2) K) (logSer (shortW g2 g3))) =
      PowerSeries.subst (at1 1 (thetaS l g2 g3 ε)) (logSer (shortW g2 g3)) :=
    Pair.subst_single_var hs (1 : Fin 2) (logSer (shortW g2 g3))
  rw [e0, e1, hlog 0, hlog 1, thetaS_eq, ← Pair.ps_comp hF0 ha, subst_C_mul hF0, hFl, mul_add]
end Formalism.L2.Th1.D
