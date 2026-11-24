-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.formal_inverse_unit_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:00.67729+00:00
-- url     : https://prove2.me/submissions/aded9069-43d7-4607-90fb-724ec3e821df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_div_diag
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis0
import Theorems.Thm_Formalism_L2_Th1_B_law_eq_of_log
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_FI
import Theorems.Thm_Formalism_L2_Th1_B_law_right_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_subst_zero
import Theorems.Thm_Formalism_L2_Th1_B_log_subst_formal_inverse
import Theorems.Thm_Formalism_L2_Th1_B_subst_at_variable_eq_subst
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution : FIUnit := by
  intro K _ _ _ F l i hF hi
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_series_at_variable 1 i hi.1
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] (FI F i) = 0 := by
    have hb := hs2 c1 c1
    unfold FI
    rw [subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]
    refine law_eq_of_log hF _ _ 0 c1 (constantCoeff_series_at_variable 1 i hi.1) cz ?_
    rw [law_subst_zero l hF.2.2.1]
    have := log_subst_formal_inverse hi (1 : Fin 2)
    change PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l +
      PowerSeries.subst (at1 (1 : Fin 2) i) l = 0
    rw [this]
    exact add_neg_cancel _
  obtain ⟨n, hn, e⟩ := div_diag (law_integral_FI hF hi) hd
  refine ⟨n, hn, ?_, e⟩
  have h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (FI F i) = 1 := by
    have hb := hs2 c0 cz
    rw [law_coeff_axis0 _ _ (by simp)]
    unfold FI
    rw [subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]
    have e0 : PowerSeries.subst ((![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) K) 1) i =
        0 := PowerSeries.subst_zero_of_constantCoeff_zero hi.1
    rw [e0]
    change MvPowerSeries.coeff _ (MvPowerSeries.subst ![MvPowerSeries.X 0, 0] F) = 1
    rw [law_right_zero hF _ c0]
    simp [MvPowerSeries.coeff_X]
  rw [e, sub_mul, map_sub] at h1
  have a0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 0 * n) =
      MvPowerSeries.constantCoeff n := by
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (0 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 1 * n) = 0 := by
    have hx : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 1 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  rw [a0, a1, sub_zero] at h1
  exact h1
end Formalism.L2.Th1.B.E2
