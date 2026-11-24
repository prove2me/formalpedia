-- Prove2me | solution 1 for Formalism.G.LogP.logF_isLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:08.22246+00:00
-- url     : https://prove2.me/submissions/5d88b0e6-722d-42ac-aec0-47bb11fa2208

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogP_omega_key
import Theorems.Thm_Formalism_G_LogP_psubst_one
import Theorems.Thm_Formalism_G_LogP_eq_zero_of_pderiv_one
import Theorems.Thm_Formalism_G_LogP_omega_mul_lam
import Theorems.Thm_Formalism_G_LogP_derivative_logF
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)
variable [Algebra ℚ R]
namespace Formalism.G.LogP
theorem _root_.solution : IsLog F (logF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hFs : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero hFc
  have hX1s : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX1
  have hc0 : PowerSeries.constantCoeff (logF F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk, if_pos rfl]
  refine ⟨hc0, ?_, ?_⟩
  · rw [logF, PowerSeries.coeff_mk, if_neg one_ne_zero, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, lam, PowerSeries.constantCoeff_invOfUnit]
    simp
  · have hω := omega_mul_lam F
    have hF1 : (lam F).subst F.toPowerSeries * (omegaF F).subst F.toPowerSeries = 1 := by
      rw [← PowerSeries.subst_mul hFs, mul_comm, hω, psubst_one hFs]
    have hY1 : atY (lam F) * atY (omegaF F) = 1 := by
      rw [atY, atY, ← PowerSeries.subst_mul hX1s, mul_comm, hω, psubst_one hX1s]
    have hk := omega_key F
    have hD : MvPowerSeries.pderiv R 1
        ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)) = 0 := by
      rw [map_sub, map_sub, pderiv_psubst hFc, atX, atY, pderiv_psubst hX0, pderiv_psubst hX1,
        derivative_logF, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      linear_combination (-((lam F).subst F.toPowerSeries *
        MvPowerSeries.pderiv R 1 F.toPowerSeries)) * hY1 + atY (lam F) * hF1 -
        (lam F).subst F.toPowerSeries * atY (lam F) * hk
    have hc2 : MvPowerSeries.HasSubst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] := hs2 (by simp) (by simp)
    have h0 : ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)).subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0 := by
      rw [subst_sub hc2, subst_sub hc2, atX, atY, psubst_subst _ hFc hc2, psubst_subst _ hX0 hc2,
        psubst_subst _ hX1 hc2, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX0),
        subst_X hc2, subst_X hc2]
      simp [PowerSeries.subst_zero_of_constantCoeff_zero hc0]
    have := eq_zero_of_pderiv_one hD h0
    rw [sub_sub, sub_eq_zero] at this
    exact this
end Formalism.G.LogP
