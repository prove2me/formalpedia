-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.density_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:32.002331+00:00
-- url     : https://prove2.me/submissions/1c89d62d-dbfa-460b-9818-bbfeac17a3c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_cayley_isometry
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_skew_of
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_map_Lp
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_eval_dp
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_eval_hq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Matrix MvPolynomial
open scoped ComplexOrder
open DensPf
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution : Dens := by
  intro n G hGpd p hp g hg
  have hH : Gᴴ = G := hGpd.1
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hGpd.isUnit
  have hzero : hq G p * dp G = 0 := by
    apply funext_set (fun _ => Set.range Complex.ofReal)
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro z hz
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_range, true_implies] at hz
    choose r hr using hz
    have hz' : z = fun v => (r v : ℂ) := funext fun v => (hr v).symm
    subst hz'
    set P : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun i j => (r (true, i, j) : ℂ) + Complex.I * r (false, i, j)) with hPdef
    have hA : (eval (fun v => (r v : ℂ))).mapMatrix (Lp G) = P - G⁻¹ * Pᴴ * G := by
      rw [map_Lp]
      congr 3
      ext i j
      simp only [hPdef, conjTranspose_apply, of_apply, star_add, star_mul', Complex.star_def,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [map_zero, map_mul]
    by_cases hd : det (1 + (P - G⁻¹ * Pᴴ * G)) = 0
    · rw [eval_dp, hA, hd, mul_zero]
    · rw [eval_hq G p _ _ hA hd, hp _ (cayley_isometry G _ (skew_of G P hH hGu) (isUnit_iff_ne_zero.2 hd)),
        mul_zero, zero_mul]
  have hB : (1 + g) * (1 + g)⁻¹ = 1 := mul_nonsing_inv _ hg
  have hB' : (1 + g)⁻¹ * (1 + g) = 1 := nonsing_inv_mul _ hg
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y = (1 - g) * (1 + g)⁻¹ := ⟨_, rfl⟩
  have hY1 : 1 + Y = (2 : ℂ) • (1 + g)⁻¹ := by
    calc 1 + Y = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [hB, hY]
      _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := by rw [← add_mul]
      _ = (2 : ℂ) • (1 + g)⁻¹ := by
        rw [show (1 + g) + (1 - g) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) by rw [two_smul]; abel,
          Matrix.smul_mul, Matrix.one_mul]
  have hY2 : 1 - Y = (2 : ℂ) • (g * (1 + g)⁻¹) := by
    calc 1 - Y = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [hB, hY]
      _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := by rw [← sub_mul]
      _ = (2 : ℂ) • (g * (1 + g)⁻¹) := by
        rw [show (1 + g) - (1 - g) = (2 : ℂ) • g by rw [two_smul]; abel, Matrix.smul_mul]
  have hR : (1 + Y) * ((1 / 2 : ℂ) • (1 + g)) = 1 := by
    rw [hY1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB']
    norm_num
  have hYu : IsUnit (1 + Y).det := isUnit_det_of_right_inverse hR
  have hcay : (1 - Y) * (1 + Y)⁻¹ = g := by
    rw [inv_eq_right_inv hR, hY2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hB',
      Matrix.mul_one]
    norm_num
  let z0 : Bool × Fin n × Fin n → ℂ := fun v => if v.1 then Y v.2.1 v.2.2 / 2
    else -Complex.I * Y v.2.1 v.2.2 / 2
  have hA0 : (eval z0).mapMatrix (Lp G) = Y := by
    rw [map_Lp]
    have hP0 : Matrix.of (fun i j => z0 (true, i, j) + Complex.I * z0 (false, i, j)) = Y := by
      ext i j
      simp only [z0, of_apply, if_true, Bool.false_eq_true, if_false]
      linear_combination (-(Y i j) / 2) * Complex.I_sq
    have hQ0 : Matrix.of (fun i j => z0 (true, j, i) - Complex.I * z0 (false, j, i)) = 0 := by
      ext i j
      simp only [z0, of_apply, if_true, Bool.false_eq_true, if_false, Matrix.zero_apply]
      linear_combination (Y j i / 2) * Complex.I_sq
    rw [hP0, hQ0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
  have hd0 : det (1 + Y) ≠ 0 := hYu.ne_zero
  have h := congrArg (eval z0) hzero
  rw [map_mul, map_zero, eval_hq G p z0 Y hA0 hd0, eval_dp, hA0, hcay] at h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h (pow_ne_zero _ hd0)
    · exact h
  · exact absurd h hd0
end Formalism.L2.SG.Pf.ColDictValCPf
