-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.lattice_sum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:31.80672+00:00
-- url     : https://prove2.me/submissions/96a0dee5-f90e-4fe5-a2f6-9912f1644fd7

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_psi_nonneg
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_tsum_psi_nonneg
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_min_pow_le
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_min_le_psi
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_cell_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.Z.LatSum := by
  classical
  refine ⟨((∑' n, psi n) + 1) ^ 2, by have := tsum_psi_nonneg; positivity, ?_⟩
  intro f La x K S hLa hx hxprod hK hS
  set D := ∑' n, psi n with hD
  have hD0 : 0 ≤ D := tsum_psi_nonneg

  let c : (Fin f → ℂ) → (Fin f → ℤ × ℤ) := fun o v =>
    (⌊2 * (o v).re / x v⌋, ⌊2 * (o v).im / x v⌋)
  have hne : ∀ o ∈ S, ∀ v, o v ≠ 0 := by
    intro o ho v h0
    have h1 := hLa o (hS o ho).1 (hS o ho).2
    rw [prod_eq_zero (mem_univ v) (by simp [h0])] at h1
    linarith

  have hinj : Set.InjOn c S := by
    intro o ho o' ho' hc
    by_contra hoo
    have hmem : o - o' ∈ La := La.sub_mem (hS o ho).1 (hS o' ho').1
    have h1 := hLa (o - o') hmem (sub_ne_zero.mpr hoo)
    have h2 : ∏ v, ‖(o - o') v‖ ≤ ∏ v, x v := by
      apply prod_le_prod (fun v _ => norm_nonneg _)
      intro v _
      have hcv := congrFun hc v
      simp only [c, Prod.mk.injEq] at hcv
      have hre := Int.abs_sub_lt_one_of_floor_eq_floor hcv.1
      have him := Int.abs_sub_lt_one_of_floor_eq_floor hcv.2
      have hxv := hx v
      have e1 : 2 * (o v).re / x v - 2 * (o' v).re / x v = 2 * ((o v).re - (o' v).re) / x v := by
        ring
      have e2 : 2 * (o v).im / x v - 2 * (o' v).im / x v = 2 * ((o v).im - (o' v).im) / x v := by
        ring
      rw [e1, abs_div, abs_mul, abs_of_pos hxv, div_lt_one hxv] at hre
      rw [e2, abs_div, abs_mul, abs_of_pos hxv, div_lt_one hxv] at him
      have h3 := Complex.norm_le_abs_re_add_abs_im ((o - o') v)
      simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im] at h3 ⊢
      norm_num at hre him
      linarith
    linarith

  have hpt : ∀ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
      ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) := by
    intro o ho
    have hno : ∀ v, 0 < ‖o v‖ := fun v => norm_pos_iff.mpr (hne o ho v)
    have ht : ∀ v, 0 < x v / ‖o v‖ := fun v => div_pos (hx v) (hno v)
    calc ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ ∏ v, ((x v / ‖o v‖) ^ ((K : ℝ) - 5 / 2) *
            ((min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ) * (min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ))) := by
          apply prod_le_prod
          · intro v _
            exact le_min zero_le_one (pow_nonneg (ht v).le _)
          · intro v _
            exact min_pow_le _ (ht v) K hK
      _ = (∏ v, (x v / ‖o v‖) ^ ((K : ℝ) - 5 / 2)) *
            ∏ v, ((min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ) * (min 1 (x v / ‖o v‖)) ^ (5 / 4 : ℝ)) := by
          rw [prod_mul_distrib]
      _ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) := by
          have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
          apply mul_le_mul
          · rw [Real.finsetProd_rpow _ _ (fun v _ => (ht v).le)]
            apply Real.rpow_le_rpow (prod_nonneg fun v _ => (ht v).le) _ (by linarith)
            rw [prod_div_distrib]
            exact div_le_self (prod_nonneg fun v _ => (hx v).le) (hLa o (hS o ho).1 (hS o ho).2)
          · apply prod_le_prod
            · intro v _
              have h0 : 0 ≤ min 1 (x v / ‖o v‖) := le_min zero_le_one (ht v).le
              positivity
            · intro v _
              have h0 : 0 ≤ min 1 (x v / ‖o v‖) := le_min zero_le_one (ht v).le
              apply mul_le_mul
              · exact min_le_psi _ _ _ (hx v) (hno v) (Complex.abs_re_le_norm _)
              · exact min_le_psi _ _ _ (hx v) (hno v) (Complex.abs_im_le_norm _)
              · positivity
              · exact psi_nonneg _
          · exact prod_nonneg fun v _ =>
              mul_nonneg (Real.rpow_nonneg (le_min zero_le_one (ht v).le) _)
                (Real.rpow_nonneg (le_min zero_le_one (ht v).le) _)
          · exact Real.rpow_nonneg (prod_nonneg fun v _ => (hx v).le) _
  have hX0 : 0 ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) :=
    Real.rpow_nonneg (prod_nonneg fun v _ => (hx v).le) _
  calc ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
      ≤ ∑ o ∈ S, (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∏ v, (psi (c o v).1 * psi (c o v).2) :=
        sum_le_sum hpt
    _ = (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ∑ p ∈ S.image c, ∏ v, (psi (p v).1 * psi (p v).2) := by
        rw [← mul_sum, sum_image (fun a ha b hb h => hinj ha hb h)]
    _ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * (D ^ 2) ^ f :=
        mul_le_mul_of_nonneg_left (cell_sum_le f _) hX0
    _ ≤ (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * ((D + 1) ^ 2) ^ f := by
        apply mul_le_mul_of_nonneg_left _ hX0
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
    _ = ((D + 1) ^ 2) ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) := mul_comm _ _
end Formalism.NuclearRankWeightBounds.P
