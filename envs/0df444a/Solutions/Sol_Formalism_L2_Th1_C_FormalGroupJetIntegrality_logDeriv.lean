-- Prove2me | solution 1 for Formalism.L2.Th1.C.FormalGroupJetIntegrality.logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:25.068477+00:00
-- url     : https://prove2.me/submissions/e74e3349-90cd-4aeb-8df1-e7ed6824b9f0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_subst_zero
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_pderiv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_substMv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_derivative_log
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_eq_substMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_zero
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_X
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.FormalGroupJetIntegrality
open JetSubstitutionLemmas
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.FormalGroupJetIntegrality
theorem _root_.solution {R : Subring K} {l linv : PowerSeries K} (h : IsLogPair l linv)
    (hF : FGInt R l linv) : IsOneUnit R (PowerSeries.derivative K l) := by
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have h10 : MvPowerSeries.pderiv K (1 : Fin 2) (MvPowerSeries.X (0 : Fin 2)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have hFc := Pts.constantCoeff_fadd h hX0 hX1
  have e1 := congrArg (MvPowerSeries.pderiv K (1 : Fin 2)) (Pts.l_fadd h hX0 hX1)
  rw [map_add, IntegralMvPolynomialLemmas.pderiv_subst _ hFc, IntegralMvPolynomialLemmas.pderiv_subst _ hX0, IntegralMvPolynomialLemmas.pderiv_subst _ hX1, h10,
    MvPowerSeries.pderiv_X_self, mul_zero, zero_add, mul_one] at e1
  have ha : ∀ s : Fin 2, IsPt R ((![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K) s) := by
    intro s
    fin_cases s
    · exact Pts.isPt_X
    · exact ⟨map_zero _, fun n => by simp⟩
  have ha0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K) s) = 0 := fun s => (ha s).1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have e2 := congrArg (MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)) e1
  rw [MvPowerSeries.subst_mul hs, Pts.substMv_subst hFc ha0, Pts.substMv_subst hX1 ha0,
    ← Pts.fadd_eq_substMv h hX (map_zero _), Pts.fadd_zero h hX, MvPowerSeries.subst_X hs] at e2
  have e3 : (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K) 1 = 0 := rfl
  have e4 : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.derivative K l) =
      PowerSeries.derivative K l := PowerSeries.X_subst _
  rw [e3, subst_zero, cc_derivative_log h, map_one, e4] at e2
  have hG : IntMv R (MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      (MvPowerSeries.pderiv K (1 : Fin 2)
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))))) :=
    IntegralMvPolynomialLemmas.intMv_substMv (IntegralMvPolynomialLemmas.intMv_pderiv hF 1) ha
  have hG0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      (MvPowerSeries.pderiv K (1 : Fin 2)
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))))) = 1 := by
    have e5 := congrArg MvPowerSeries.constantCoeff e2
    have e6 : MvPowerSeries.constantCoeff (PowerSeries.derivative K l : MvPowerSeries Unit K) = 1 :=
      cc_derivative_log h
    rwa [map_mul, e6, one_mul, map_one] at e5
  refine ⟨cc_derivative_log h, intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_of_mul_eq_one hG hG0 ?_)⟩
  rw [mul_comm]
  exact e2
end Formalism.L2.Th1.C.FormalGroupJetIntegrality
