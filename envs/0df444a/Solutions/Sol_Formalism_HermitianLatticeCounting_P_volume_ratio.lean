-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.volume_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:37.701806+00:00
-- url     : https://prove2.me/submissions/b4741d08-06fe-4efa-a41c-10455125dbcc

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_vsph_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_vsph_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sfac_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sfac_prod_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_inv_sfac_le_vsph
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_vratio_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : VRatio := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨2 * Real.pi * Real.exp 1, by nlinarith, ?_⟩
  intro p q a j hJq hqp
  have hPi : (sfac (∑ x, j x))⁻¹ ≤ ∏ x, Vsph (j x) := by
    calc (sfac (∑ x, j x))⁻¹ ≤ (∏ x, sfac (j x))⁻¹ := by
          apply inv_anti₀ (Finset.prod_pos fun x _ => sfac_pos _) (sfac_prod_le _ _)
      _ = ∏ x, (sfac (j x))⁻¹ := (Finset.prod_inv_distrib _).symm
      _ ≤ _ := Finset.prod_le_prod (fun x _ => (inv_pos.mpr (sfac_pos _)).le)
          (fun x _ => inv_sfac_le_vsph _)
  generalize (∏ x, Vsph (j x)) = Pj at *
  generalize (∑ x, j x) = J at *
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hJq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_trans (Nat.le_add_left J k') hqp)
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, vsph_add k J, vsph_add k' J]
  have hS := sfac_pos J
  have hPj : 0 < Pj := lt_of_lt_of_le (inv_pos.mpr hS) hPi
  have hVk := vsph_pos k
  have hVk' := vsph_pos k'
  set P1 := ∏ i ∈ range J, (2 * Real.pi ^ (k + i + 1) / ((k + i).factorial : ℝ)) with hP1
  set P2 := ∏ i ∈ range J, (2 * Real.pi ^ (k' + i + 1) / ((k' + i).factorial : ℝ)) with hP2
  have hP10 : 0 ≤ P1 := Finset.prod_nonneg fun i _ => by positivity
  have hP20 : 0 ≤ P2 := Finset.prod_nonneg fun i _ => by positivity
  have e : Vsph k * P1 * (Vsph k' * P2) / (Vsph k * Vsph k' * Pj) = P1 * P2 / Pj := by
    field_simp
  rw [e]
  have b1 : P1 ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ)) ^ J := by
    rw [hP1]
    conv_rhs => rw [← Finset.card_range J, ← Finset.prod_const, Finset.card_range]
    apply Finset.prod_le_prod (fun i _ => by positivity)
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 : Real.pi ^ (k + i + 1) ≤ Real.pi ^ (k + J) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : (k.factorial : ℝ) ≤ ((k + i).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    gcongr
  have b2 : P2 ≤ (2 * Real.pi ^ (k' + J)) ^ J * (sfac J)⁻¹ := by
    rw [hP2]
    unfold sfac
    rw [← Finset.prod_inv_distrib]
    conv_rhs => rw [← Finset.card_range J, ← Finset.prod_const, Finset.card_range]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _ => by positivity)
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 : Real.pi ^ (k' + i + 1) ≤ Real.pi ^ (k' + J) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : (i.factorial : ℝ) ≤ ((k' + i).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0:ℝ) < i.factorial := by exact_mod_cast i.factorial_pos
    rw [← div_eq_mul_inv]
    gcongr
  have hJJ : 1 ≤ (J:ℝ) ^ ((J:ℝ) ^ 2 / 2) := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · exact Real.one_le_rpow (by exact_mod_cast hJ) (by positivity)
  have b3 : P1 * P2 / Pj ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ) * (2 * Real.pi ^ (k' + J))) ^ J := by
    calc P1 * P2 / Pj ≤ P1 * P2 / (sfac J)⁻¹ := by gcongr
      _ = P1 * (P2 * sfac J) := by rw [div_inv_eq_mul]; ring
      _ ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ)) ^ J
            * ((2 * Real.pi ^ (k' + J)) ^ J * (sfac J)⁻¹ * sfac J) := by gcongr
      _ = _ := by
          rw [mul_assoc ((2 * Real.pi ^ (k' + J)) ^ J), inv_mul_cancel₀ hS.ne', mul_one, ← mul_pow]
  have b4 : (2 * Real.pi ^ (k + J) / (k.factorial : ℝ) * (2 * Real.pi ^ (k' + J))) ^ J
      ≤ (2 * Real.pi * Real.exp 1) ^ (J * (k + J + (k' + J)))
        * ((2 * Real.pi * Real.exp 1) / ((k + J : ℕ):ℝ)) ^ (J * k) := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · rw [mul_comm J, mul_comm J, pow_mul, pow_mul, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      exact vratio_base (k + J) (k' + J) k (by omega) (by omega)
  calc P1 * P2 / Pj ≤ _ := b3
    _ ≤ _ := b4
    _ = (2 * Real.pi * Real.exp 1) ^ (J * (k + J + (k' + J)))
        * ((2 * Real.pi * Real.exp 1) / ((k + J : ℕ):ℝ)) ^ (J * k) * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
