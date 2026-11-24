-- Prove2me | solution 1 for Formalism.G.LogP.omega_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:03.574164+00:00
-- url     : https://prove2.me/submissions/9f6485e3-400f-42a3-8992-d8e66a7d07e1

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_G_LogP_omega_subst
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst


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
namespace Formalism.G.LogP
theorem _root_.solution :
    (omegaF F).subst F.toPowerSeries =
      MvPowerSeries.pderiv R 1 F.toPowerSeries * atY (omegaF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hY : ∀ i, constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = 0 := fun i => by
    simp
  have hG : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have hH : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have dG : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp)]
    simp [Fin.sum_univ_two, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide),
      pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  have dH : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2] := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp)]
    simp [Fin.sum_univ_two, pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  have E := congrArg (MvPowerSeries.pderiv R 2) F.assoc
  rw [pderiv_subst (fun i => by fin_cases i <;> simp [hG]),
    pderiv_subst (fun i => by fin_cases i <;> simp [hH])] at E
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, dG, dH, pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide), mul_zero, zero_add, mul_one] at E
  have hc3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0] :=
    hs3 (by simp) (by simp) (by simp)
  have E' := congrArg (MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0]) E
  rw [subst_mul hc3, subst2_subst _ hG (hY 2) hc3, subst2_subst _ (hY 0) hH hc3,
    subst2_subst _ (hY 1) (hY 2) hc3, subst2_subst _ (hY 0) (hY 1) hc3,
    subst2_subst _ (hY 1) (hY 2) hc3] at E'
  simp only [subst_X hc3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at E'
  rw [subst_XX, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX1), subst_XX] at E'
  rw [omega_subst hFc, atY, omega_subst hX1]
  exact E'
end Formalism.G.LogP
