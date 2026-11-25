-- Prove2me | solution 1 for Formalism.L2.Th1.C.FormalGroupJetIntegrality.third
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:53:37.305942+00:00
-- url     : https://prove2.me/submissions/50b0f5b6-6fe9-43cb-bcb5-45b3beea47c2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_ph_fadd
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_pderiv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst_l
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intMv_X
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_fadd
import Theorems.Thm_P2M_Formalism_L2_Th1_C_expIntegralDeriv__70ca0e7dcf2b


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
variable {K : Type} [Field K] [CharZero K] {R : Subring K}
namespace Formalism.L2.Th1.C.FormalGroupJetIntegrality
theorem _root_.solution {l linv ph : PowerSeries K} (hFr : Frame R l linv ph) (hF1 : F1 R l linv ph) :
    IntMv R (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
          PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
          PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l)
        ((PowerSeries.derivative K)^[3] (PowerSeries.subst linv ph)) *
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l) *
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l) *
      PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l)) := by
  have h := hFr.1
  have hX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X _
  have hP : ∀ i : Fin 3, IsPt R (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) :=
    fun i => ⟨hX i, Pts.intMv_X i⟩
  have hz : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) l) = 0 :=
    fun i => Pts.constantCoeff_subst_l h (hX i)
  have hzz : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) l) = 0 :=
    fun i j => by rw [map_add, hz, hz, add_zero]
  have hzzz : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l) = 0 := by
    rw [map_add, hzz, hz, add_zero]
  have h01 : MvPowerSeries.pderiv K (0 : Fin 3) (MvPowerSeries.X (1 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h02 : MvPowerSeries.pderiv K (0 : Fin 3) (MvPowerSeries.X (2 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h10 : MvPowerSeries.pderiv K (1 : Fin 3) (MvPowerSeries.X (0 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h12 : MvPowerSeries.pderiv K (1 : Fin 3) (MvPowerSeries.X (2 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h20 : MvPowerSeries.pderiv K (2 : Fin 3) (MvPowerSeries.X (0 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have h21 : MvPowerSeries.pderiv K (2 : Fin 3) (MvPowerSeries.X (1 : Fin 3)) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have hT := hF1 (Fin 3) _ _ _ (hP 0) (hP 1) (hP 2)
  have hI := IntegralMvPolynomialLemmas.intMv_pderiv (IntegralMvPolynomialLemmas.intMv_pderiv (expIntegralDeriv' K R (Fin 3) _ hT 0) 1) 2
  unfold be0 at hI
  rw [ph_fadd h ph (Pts.constantCoeff_fadd h (hX 0) (hX 1)) (hX 2), Pts.l_fadd h (hX 0) (hX 1),
    ph_fadd h ph (hX 0) (hX 1), ph_fadd h ph (hX 0) (hX 2), ph_fadd h ph (hX 1) (hX 2)] at hI
  simp only [IntegralMvPolynomialLemmas.pderiv_subst _ hzzz, IntegralMvPolynomialLemmas.pderiv_subst _ (hzz _ _), IntegralMvPolynomialLemmas.pderiv_subst _ (hX _),
    map_add, map_sub, Derivation.leibniz, MvPowerSeries.pderiv_X_self, h01, h02, h10, h12, h20, h21,
    smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, sub_zero, sub_self] at hI
  have e : (PowerSeries.derivative K)^[3] (PowerSeries.subst linv ph) =
      PowerSeries.derivative K (PowerSeries.derivative K (PowerSeries.derivative K
        (PowerSeries.subst linv ph))) := rfl
  rw [e]
  convert hI using 1
  ring
end Formalism.L2.Th1.C.FormalGroupJetIntegrality
