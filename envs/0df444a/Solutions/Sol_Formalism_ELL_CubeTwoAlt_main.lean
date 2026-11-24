-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:06.545626+00:00
-- url     : https://prove2.me/submissions/98d81f19-e042-49f3-a1ba-7fde0afc44b5

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_div_diag
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_subst_wU_X_mem_T_of_wFixed
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_U_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_Wi_eq
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_Fp_diag
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_chord_subst_inverse_mem
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_Fp_lin
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_C3_mem_T_of_wFixed
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_dd_mem_T_of_wFixed
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_X
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_ne
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constSeries_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_chordCoeffCubic
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_dd_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_intercept_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_inv_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_nu_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_vieta
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_weq_iff
import Theorems.Thm_Formalism_ELL_wSeriesSubstUnique_holds
import Theorems.Thm_P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (hw : WFixed W w) :
    ∃ c : MvPowerSeries (Fin 2) K, c ∈ T W ∧ cc c = -1 ∧
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))⁻¹
        - (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))⁻¹
        = c * WeierstrassChordSeries.F2 W w * MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
            (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] (WeierstrassChordSeries.F2 W w) := by
  have : IsDomain (MvPowerSeries (Fin 2) K) := NoZeroDivisors.to_isDomain _
  have hU := wSeriesSubstUnique_holds.{u}
  obtain ⟨Q, hQT, hQ⟩ := div_diag _ (chord_subst_inverse_mem hw) (Fp_diag hw)
  have hQc : cc Q = -1 := by
    have h := Fp_lin hw
    rw [hQ, WeierstrassChordSeries.L_mul] at h
    simpa [WeierstrassChordSeries.L_X] using h

  have hUs := fun (s : MvPowerSeries (Fin 2) K) (hs : cc s = 0) => hU K W w hw (Fin 2) s hs
  have h0 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 0) (by simp)).1
  have h1 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 1) (by simp)).1
  have hW0 : Wi w 0 = lam w * MvPowerSeries.X 0 + nu w := by unfold nu; ring
  have hW1 : Wi w 1 = lam w * MvPowerSeries.X 1 + nu w := by
    have := lam_mul w; unfold nu; linear_combination -this
  change WeierstrassChordSeries.G _ _ _ _ _ _ (Wi w 0) = 0 at h0
  change WeierstrassChordSeries.G _ _ _ _ _ _ (Wi w 1) = 0 at h1
  have hinv : C3 W w * (C3 W w)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero)
  have he1 : c3 (ca W.a₂) (ca W.a₄) (ca W.a₆) (lam w) *
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + z3 W w) +
      c2 (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) (lam w) (nu w) = 0 := by
    change C3 W w * _ + C2 W w = 0
    rw [z3]
    linear_combination (-C2 W w) * hinv
  rw [hW0] at h0
  rw [hW1] at h1
  obtain ⟨-, -, he3⟩ := vieta X_ne h0 h1 he1
  change C3 W w * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * z3 W w)
    + c0 (ca W.a₃) (ca W.a₆) (nu w) = 0 at he3
  simp only [c0] at he3
  obtain ⟨Ua, hUa⟩ : ∃ U, U = (wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ U, U = (wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : MvPowerSeries (Fin 2) K,
      E = 1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2 := ⟨_, rfl⟩
  have hUac : cc Ua = 1 := hUa ▸ U_cc hw 0
  have hUbc : cc Ub = 1 := hUb ▸ U_cc hw 1
  have hEc : cc E = 1 := by rw [hE]; simp [nu_cc hw]
  have hIa : Ua * Ua⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hUac]; exact one_ne_zero)
  have hIb : Ub * Ub⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hUbc]; exact one_ne_zero)
  have hIe : E * E⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hEc]; exact one_ne_zero)
  have hIq : Q * Q⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hQc]; exact neg_ne_zero.mpr one_ne_zero)
  have hWa : Wi w 0 = MvPowerSeries.X 0 ^ 3 * Ua := hUa ▸ Wi_eq hw 0
  have hWb : Wi w 1 = MvPowerSeries.X 1 ^ 3 * Ub := hUb ▸ Wi_eq hw 1
  have hlam := lam_mul w
  have hν2 : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * nu w =
      MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ 3 * Ua
        - MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 3 * Ub := by
    unfold nu
    linear_combination (-MvPowerSeries.X 0) * hlam + MvPowerSeries.X 1 * hWa
      - MvPowerSeries.X 0 * hWb
  have key0 : MvPowerSeries.X 0 * MvPowerSeries.X 1 *
      ((MvPowerSeries.X 1 - MvPowerSeries.X 0) * C3 W w * z3 W w
        + (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * Ua * Ub * E) = 0 := by
    rw [hE]
    linear_combination (MvPowerSeries.X 1 - MvPowerSeries.X 0) * he3
      + (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 1 ^ 2 * Ub
        * (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2)) * hIa
      - (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ 2 * Ua
        * (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2)) * hIb
      + (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2) * hν2
  have key1 := (mul_eq_zero.mp key0).resolve_left
    (mul_ne_zero (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (WeierstrassCoordinateSubstitution.X_ne_zero' 1))
  have hdc : cc (dd W w) ≠ 0 := by rw [dd_cc hw]; exact neg_ne_zero.mpr one_ne_zero
  have hF : WeierstrassChordSeries.F2 W w * dd W w = z3 W w := by
    rw [WeierstrassChordSeries.F2, mul_assoc, mul_comm _ (dd W w), MvPowerSeries.mul_inv_cancel _ hdc, mul_one]
  rw [← hF] at key1
  refine ⟨-(C3 W w * dd W w * Ua⁻¹ * Ub⁻¹ * E⁻¹ * Q⁻¹), ?_, ?_, ?_⟩
  · have hUaT : Ua⁻¹ ∈ T W := inv_mem_integralSeries (hUa ▸ subst_wU_X_mem_T_of_wFixed hw 0) (by rw [hUac]; exact one_ne_zero)
      (by rw [hUac, inv_one]; exact Subalgebra.one_mem _)
    have hUbT : Ub⁻¹ ∈ T W := inv_mem_integralSeries (hUb ▸ subst_wU_X_mem_T_of_wFixed hw 1) (by rw [hUbc]; exact one_ne_zero)
      (by rw [hUbc, inv_one]; exact Subalgebra.one_mem _)
    have hET : E ∈ T W := by
      rw [hE]
      exact (T W).sub_mem ((T W).sub_mem (T W).one_mem
        ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) (intercept_mem_integralSeries hw)))
        ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) ((T W).pow_mem (intercept_mem_integralSeries hw) 2))
    have hEiT : E⁻¹ ∈ T W := inv_mem_integralSeries hET (by rw [hEc]; exact one_ne_zero)
      (by rw [hEc, inv_one]; exact Subalgebra.one_mem _)
    have hQiT : Q⁻¹ ∈ T W := inv_mem_integralSeries hQT (by rw [hQc]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [hQc, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
    exact (T W).neg_mem ((T W).mul_mem ((T W).mul_mem ((T W).mul_mem ((T W).mul_mem
      ((T W).mul_mem (C3_mem_T_of_wFixed hw) (dd_mem_T_of_wFixed hw)) hUaT) hUbT) hEiT) hQiT)
  · simp [MvPowerSeries.constantCoeff_inv, constantCoeff_chordCoeffCubic hw, dd_cc hw, hUac, hUbc, hEc, hQc]
  · rw [hQ, ← hUa, ← hUb]
    linear_combination (Ua⁻¹ * Ub⁻¹ * E⁻¹ * Q⁻¹ * Q) * key1
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (Ub * Ub⁻¹) * (E * E⁻¹)
        * (Q * Q⁻¹) * hIa
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (E * E⁻¹) * (Q * Q⁻¹) * hIb
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (Q * Q⁻¹) * hIe
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * hIq
end Formalism.ELL.CubeTwoAlt
