-- Prove2me | solution 1 for Formalism.L2.Th1.C.FormalGroupJetIntegrality.integral_third_invariant_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:30.516538+00:00
-- url     : https://prove2.me/submissions/0a1e8d83-7d58-4de9-a2b1-12a7bee5ad61

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_subst_zero
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_logDeriv
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_third
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_substMv
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_derivative_log
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_mul
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_Dinv_iterate
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst_l
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_X
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_mul
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_of_mul_eq_one


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
    IntPS R ((Dinv l)^[3] ph) := by
  have h := hFr.1
  have hl := logDeriv h hFr.2.1
  have hX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X _
  have hz : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) l) = 0 :=
    fun i => Pts.constantCoeff_subst_l h (hX i)
  have hzzz : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l) = 0 := by
    rw [map_add, map_add, hz, hz, hz, add_zero, add_zero]
  have ha : ∀ s : Fin 3, IsPt R ((![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) s) := by
    intro s
    fin_cases s
    · exact Pts.isPt_X
    · exact ⟨map_zero _, fun n => by simp⟩
    · exact ⟨map_zero _, fun n => by simp⟩
  have ha0 : ∀ s : Fin 3, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) s) = 0 := fun s => (ha s).1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hI := IntegralMvPolynomialLemmas.intMv_substMv (third hFr hF1) ha
  have a0 : (![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) 0 = PowerSeries.X := rfl
  have a1 : (![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) 1 = 0 := rfl
  have a2 : (![PowerSeries.X, 0, 0] : Fin 3 → MvPowerSeries Unit K) 2 = 0 := rfl
  have eX : ∀ g : PowerSeries K, PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) g = g :=
    fun g => PowerSeries.X_subst g
  rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_mul hs,
    Pts.substMv_subst hzzz ha0, Pts.substMv_subst (hX 0) ha0, Pts.substMv_subst (hX 1) ha0,
    Pts.substMv_subst (hX 2) ha0, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    Pts.substMv_subst (hX 0) ha0, Pts.substMv_subst (hX 1) ha0, Pts.substMv_subst (hX 2) ha0,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs, a0, a1, a2,
    subst_zero, subst_zero, cc_derivative_log h, h.1, map_zero, map_one, add_zero, add_zero,
    mul_one, mul_one, eX, eX, ← subst_Dinv_iterate h] at hI
  have hl0 : MvPowerSeries.constantCoeff (l : MvPowerSeries Unit K) = 0 := h.1
  rw [Pts.subst_subst h.2.2.1 hl0, h.2.2.2.1, eX] at hI
  have hne : PowerSeries.constantCoeff (PowerSeries.derivative K l) ≠ 0 := by
    rw [hl.1]; exact one_ne_zero
  have hinv : IntPS R (PowerSeries.derivative K l)⁻¹ :=
    intPS_of_mul_eq_one hl.2 hl.1 (PowerSeries.mul_inv_cancel _ hne)
  have e : (Dinv l)^[3] ph =
      ((Dinv l)^[3] ph * PowerSeries.derivative K l) * (PowerSeries.derivative K l)⁻¹ := by
    rw [mul_assoc, PowerSeries.mul_inv_cancel _ hne, mul_one]
  rw [e]
  exact intPS_mul (intPS_of_intMv hI) hinv
end Formalism.L2.Th1.C.FormalGroupJetIntegrality
