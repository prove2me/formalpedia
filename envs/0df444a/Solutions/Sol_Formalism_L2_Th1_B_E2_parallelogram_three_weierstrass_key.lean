-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.parallelogram_three_weierstrass_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:01.467624+00:00
-- url     : https://prove2.me/submissions/38c9e55b-746a-434c-90e7-cc45d61b531e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_fExp_three
import Theorems.Thm_Formalism_L2_Th1_B_E2_curve3_at
import Theorems.Thm_Formalism_L2_Th1_B_E2_subst_det_three_points
import Theorems.Thm_Formalism_L2_Th1_B_E2_subst_series_at_sum_three
import Theorems.Thm_Formalism_L2_Th1_B_E2_subst_series_at_difference_three
import Theorems.Thm_Formalism_L2_Th1_B_E2_det_rows
import Theorems.Thm_Formalism_L2_Th1_B_E2_inVar_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_E2_sum_log_three_variables_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_E2_cX
import Theorems.Thm_Formalism_L2_Th1_B_E2_constantCoeff_law_three_variables
import Theorems.Thm_Formalism_L2_Th1_B_E2_log_formal_law_three_variables
import Theorems.Thm_Formalism_L2_Th1_B_E2_constantCoeff_law_with_inverse_three
import Theorems.Thm_Formalism_L2_Th1_B_E2_log_law_with_inverse_three
import Theorems.Thm_Formalism_L2_Th1_B_E2_law_with_inverse_factor_difference
import Theorems.Thm_Formalism_L2_Th1_B_E2_X_sub_ne_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_curve_at
import Theorems.Thm_Formalism_L2_Th1_B_ParO_fExp_mul_neg
import Theorems.Thm_Formalism_L2_Th1_B_ParO_inVar_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_ne_zero_of_psubst
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_value_at
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_phODef
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
variable {K : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution (hA : FrobStickStar) {g2 g3 s2 c0 a1 a3 : K} {P l i ep : PowerSeries K}
    {F n : MvPowerSeries (Fin 2) K} {e : MvPowerSeries (Fin 3) K} (hP : IsWp g2 g3 P)
    (hF : LawLog F l) (hi : IsInv l i)
    (h2 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (h3 : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3))
    (he : Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2))
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) :
    MvPowerSeries.constantCoeff (par3 F i (phO s2 P l)) = 0 ∧
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      fExp (-par3 F i (phO s2 P l)) = -e := by
  have hl0 := hF.2.2.1
  have hl1 := hF.2.2.2.1
  obtain ⟨hph0, hphe⟩ := phODef K s2 P l hl0 hl1
  generalize phO s2 P l = ph at hph0 hphe ⊢
  have cL : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j l) = 0 :=
    fun j => constantCoeff_series_at_variable j l hl0
  have hφ : MvPowerSeries.HasSubst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero cL
  have key := congrArg (MvPowerSeries.subst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K)))
    (hA K g2 g3 s2 P hP)
  rw [← MvPowerSeries.coe_substAlgHom hφ] at key
  simp only [map_mul, map_pow, map_neg, map_ofNat] at key
  simp only [MvPowerSeries.coe_substAlgHom hφ, MvPowerSeries.subst_X hφ, subst_series_at_sum_three _ hφ,
    subst_series_at_difference_three _ _ _ hφ, subst_det_three_points _ hφ, ParO.subst_inVar _ _ hφ] at key
  have cS := constantCoeff_law_three_variables hF.1
  have cD := constantCoeff_law_with_inverse_three hF hi
  have v : ∀ j : Fin 3, PowerSeries.subst (at1 j l) (sgStar s2 P) =
      MvPowerSeries.X j * fExp (-at1 j ph) := fun j => ParO.value_at hl0 hph0 hphe (cX j)
  rw [← log_formal_law_three_variables hF, ← log_law_with_inverse_three hF hi 0 1, ← log_law_with_inverse_three hF hi 0 2, ← log_law_with_inverse_three hF hi 1 2,
    ParO.value_at hl0 hph0 hphe cS, ParO.value_at hl0 hph0 hphe (cD 0 1),
    ParO.value_at hl0 hph0 hphe (cD 0 2), ParO.value_at hl0 hph0 hphe (cD 1 2), v 0, v 1, v 2]
    at key
  have dr := det_rows (fun j : Fin 3 => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K))
    (fun j => at1 j l) (fun j => 1 + at1 j l ^ 2 * PowerSeries.subst (at1 j l) P)
    (fun j => -2 + at1 j l ^ 3 * PowerSeries.subst (at1 j l) (dz P)) (fun j => at1 j ep)
    (MvPowerSeries.C c0) (MvPowerSeries.C a1) (MvPowerSeries.C a3)
    (fun j => ParO.curve_at hl0 h2 j) (fun j => curve3_at hl0 h3 j)
  simp only [he] at dr
  have cA : MvPowerSeries.constantCoeff (PowerSeries.subst (F3 F) ph) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero cS ph hph0
  have cB : ∀ j k, MvPowerSeries.constantCoeff (PowerSeries.subst (lawDifferenceThree F i j k) ph) = 0 :=
    fun j k => PowerSeries.constantCoeff_subst_eq_zero (cD j k) ph hph0
  have ca : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j ph) = 0 :=
    fun j => constantCoeff_series_at_variable j ph hph0
  have hpar : -par3 F i ph = -PowerSeries.subst (F3 F) ph + -PowerSeries.subst (lawDifferenceThree F i 0 1) ph +
      -PowerSeries.subst (lawDifferenceThree F i 0 2) ph + -PowerSeries.subst (lawDifferenceThree F i 1 2) ph +
      3 * at1 0 ph + 3 * at1 1 ph + 3 * at1 2 ph := by
    unfold par3; ring
  have h0 : MvPowerSeries.constantCoeff (par3 F i ph) = 0 := by
    unfold par3; simp [cA, cB, ca]
  refine ⟨h0, ?_⟩
  rw [hpar, fExp_add (by simp [cA, cB, ca]) (by simp [ca]),
    fExp_add (by simp [cA, cB, ca]) (by simp [ca]), fExp_add (by simp [cA, cB]) (by simp [ca]),
    fExp_add (by simp [cA, cB]) (by simp [cB]), fExp_add (by simp [cA, cB]) (by simp [cB]),
    fExp_add (by simp [cA]) (by simp [cB]), fExp_three (ca 0), fExp_three (ca 1),
    fExp_three (ca 2)]
  have r0 := ParO.fExp_mul_neg (ca 0)
  have r1 := ParO.fExp_mul_neg (ca 1)
  have r2 := ParO.fExp_mul_neg (ca 2)
  have f01 := law_with_inverse_factor_difference hi.1 hn 0 1
  have f02 := law_with_inverse_factor_difference hi.1 hn 0 2
  have f12 := law_with_inverse_factor_difference hi.1 hn 1 2
  have hF3 : F3 F ≠ 0 := ParO.ne_zero_of_psubst hl0 (by rw [log_formal_law_three_variables hF]; exact sum_log_three_variables_ne_zero hl1)
  generalize fExp (-PowerSeries.subst (F3 F) ph) = ES at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 0 1) ph) = bivariateExponentMonomial at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 0 2) ph) = E02 at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 1 2) ph) = E12 at key ⊢
  rw [f01, f02, f12] at key
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n = n01 at key ⊢
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n02 at key ⊢
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n12 at key ⊢
  generalize fExp (-at1 (0 : Fin 3) ph) = E0 at key r0 ⊢
  generalize fExp (-at1 (1 : Fin 3) ph) = E1 at key r1 ⊢
  generalize fExp (-at1 (2 : Fin 3) ph) = E2 at key r2 ⊢
  generalize fExp (at1 (0 : Fin 3) ph) = G0 at r0 ⊢
  generalize fExp (at1 (1 : Fin 3) ph) = G1 at r1 ⊢
  generalize fExp (at1 (2 : Fin 3) ph) = G2 at r2 ⊢
  have h2ne : (2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact two_ne_zero this
  have hne : 2 * (at1 (0 : Fin 3) l * at1 1 l * at1 2 l) ^ 3 * F3 F *
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2ne
      (pow_ne_zero 3 (mul_ne_zero (mul_ne_zero (inVar_ne_zero hl1 0) (inVar_ne_zero hl1 1))
        (inVar_ne_zero hl1 2)))) hF3) (X_sub_ne_zero (by decide))) (X_sub_ne_zero (by decide)))
      (X_sub_ne_zero (by decide))
  have E : (E0 * E1 * E2) ^ 3 * e = -(n01 * n02 * n12 * (ES * bivariateExponentMonomial * E02 * E12)) := by
    refine mul_left_cancel₀ hne ?_
    linear_combination key - (E0 * E1 * E2) ^ 3 * dr
  have hp : (G0 * G1 * G2) ^ 3 * (E0 * E1 * E2) ^ 3 = 1 := by
    have : G0 * G1 * G2 * (E0 * E1 * E2) = 1 := by
      calc G0 * G1 * G2 * (E0 * E1 * E2) = (G0 * E0) * (G1 * E1) * (G2 * E2) := by ring
        _ = 1 := by rw [r0, r1, r2]; ring
    rw [← mul_pow, this, one_pow]
  linear_combination (G0 * G1 * G2) ^ 3 * E - e * hp
end Formalism.L2.Th1.B.E2
