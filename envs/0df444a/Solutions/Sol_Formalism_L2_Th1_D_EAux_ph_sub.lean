-- Prove2me | solution 1 for Formalism.L2.Th1.D.EAux.ph_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:45.397525+00:00
-- url     : https://prove2.me/submissions/35c42d28-6ec2-4ba3-af88-ff8e9785ccbf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_L2_Th1_D_EAux_cc_theta
import Theorems.Thm_Formalism_L2_Th1_D_EAux_log_theta
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
import Theorems.Thm_Formalism_L2_Th1_B_ParO_X_mul_lU
import Theorems.Thm_Formalism_L2_Th1_B_ParO_constantCoeff_lU
import Theorems.Thm_Formalism_L2_Th1_B_ParO_fLog_mul
import Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_neg
import Theorems.Thm_Formalism_L2_Th1_B_Ph_X_mul_lU
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_lU
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_C_mul
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_fLog
import Theorems.Thm_Formalism_L2_Th1_B_Ph_psubst_neg
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
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
open Formalism.L2.Th1.D.EAux
namespace Formalism.L2.Th1.D.EAux
theorem _root_.solution {K : Type} [Field K] [CharZero K] {l : ℕ} (hl : 2 ≤ l) (g2 g3 s2 : K) {ε : K}
    (hε : ε ≠ 0) :
    PowerSeries.constantCoeff (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) = 1 ∧
    phFF l g2 g3 s2 ε - PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2) =
      -fLog (PowerSeries.C ε⁻¹ * lU (thetaS l g2 g3 ε)) := by
  set θ := thetaS l g2 g3 ε with hθ
  set L := logSer (shortW g2 g3) with hL
  have hθ0 : PowerSeries.constantCoeff θ = 0 := cc_theta hl g2 g3 ε
  have hθL : PowerSeries.subst θ L = PowerSeries.C ε * lgF K l := log_theta hl g2 g3 ε
  have hLs := Formalism.L2.Th1.A.logSpec K (shortW g2 g3)
  have hL0 : PowerSeries.constantCoeff L = 0 := hLs.1
  have hL1 : PowerSeries.coeff 1 L = 1 := hLs.2.1
  have hs := Formalism.L2.Th1.B.Ph.hs hθ0
  have cU : PowerSeries.constantCoeff (lU L) = 1 :=
    (Formalism.L2.Th1.B.Ph.constantCoeff_lU L).trans hL1
  have cG : PowerSeries.constantCoeff (PowerSeries.subst θ (lU L)) = 1 := by
    rw [Formalism.L2.Th1.B.Ph.constantCoeff_psubst hθ0, cU]
  have cl : PowerSeries.constantCoeff (lU (lgF K l)) = 1 :=
    (Formalism.L2.Th1.B.Ph.constantCoeff_lU _).trans (by simpa using Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl 0)

  have hprod : PowerSeries.C ε⁻¹ * lU θ * PowerSeries.subst θ (lU L) = lU (lgF K l) := by
    have h1 : PowerSeries.subst θ L = θ * PowerSeries.subst θ (lU L) := by
      conv_lhs => rw [← Formalism.L2.Th1.B.Ph.X_mul_lU hL0, PowerSeries.subst_mul hs,
        PowerSeries.subst_X hs]
    rw [hθL] at h1
    have h2 : PowerSeries.X * (PowerSeries.C ε * lU (lgF K l)) =
        PowerSeries.X * (lU θ * PowerSeries.subst θ (lU L)) := by
      calc PowerSeries.X * (PowerSeries.C ε * lU (lgF K l))
          = PowerSeries.C ε * (PowerSeries.X * lU (lgF K l)) := by ring
        _ = PowerSeries.C ε * lgF K l := by rw [Formalism.L2.Th1.B.Ph.X_mul_lU (Pair.cc_lgF hl)]
        _ = θ * PowerSeries.subst θ (lU L) := h1
        _ = (PowerSeries.X * lU θ) * PowerSeries.subst θ (lU L) := by
            rw [Formalism.L2.Th1.B.Ph.X_mul_lU hθ0]
        _ = _ := by ring
    have h3 := mul_left_cancel₀ PowerSeries.X_ne_zero h2
    have hC : PowerSeries.C ε⁻¹ * PowerSeries.C ε = (1 : PowerSeries K) := by
      rw [← map_mul, inv_mul_cancel₀ hε, map_one]
    calc PowerSeries.C ε⁻¹ * lU θ * PowerSeries.subst θ (lU L)
        = PowerSeries.C ε⁻¹ * (lU θ * PowerSeries.subst θ (lU L)) := by ring
      _ = PowerSeries.C ε⁻¹ * PowerSeries.C ε * lU (lgF K l) := by rw [← h3]; ring
      _ = _ := by rw [hC, one_mul]
  have cV : PowerSeries.constantCoeff (PowerSeries.C ε⁻¹ * lU θ) = 1 := by
    have := congrArg PowerSeries.constantCoeff hprod
    rw [map_mul, cG, mul_one, cl] at this
    exact this
  refine ⟨cV, ?_⟩
  have hlog : fLog (lU (lgF K l)) =
      fLog (PowerSeries.C ε⁻¹ * lU θ) + fLog (PowerSeries.subst θ (lU L)) := by
    rw [← hprod]
    exact Formalism.L2.Th1.B.ParO.fLog_mul cV cG
  have hcur : PowerSeries.subst θ (phCurve g2 g3 s2) =
      -PowerSeries.subst (PowerSeries.C ε * lgF K l) (sigS (wpReg (shortW g2 g3))) +
        PowerSeries.C (s2 / 2) * (PowerSeries.C ε * lgF K l) ^ 2 -
        fLog (PowerSeries.subst θ (lU L)) := by
    unfold phCurve phO
    rw [PowerSeries.subst_sub hs, PowerSeries.subst_add hs, Formalism.L2.Th1.B.Ph.psubst_neg hθ0,
      Formalism.L2.Th1.B.Ph.psubst_C_mul hθ0, PowerSeries.subst_pow hs,
      Formalism.L2.Th1.B.Ph.psubst_fLog hθ0 cU, ← Pair.ps_comp (τ := Unit) hθ0 hL0, hθL]
  rw [hcur]
  unfold phFF
  rw [hlog]
  ring
end Formalism.L2.Th1.D.EAux
