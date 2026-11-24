-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.multiplicity_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:58.368277+00:00
-- url     : https://prove2.me/submissions/7979dbdb-119f-4f39-93f0-cab1af6efce2

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_one_sub_sum_le_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : MultProd := by
  unfold MultProd
  intro Pv _ q nn k f r g hcard hr hg hgq hfrg hb
  classical
  have hf : 0 ≤ f := by
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card Pv); linarith
  have hqpos : ∀ v, 0 < q v := fun v => lt_of_lt_of_le hg (hgq v)
  have hq1 : ∀ v, 1 ≤ q v := by
    intro v
    have hc : (1:ℝ) ≤ (Fintype.card Pv : ℝ) := Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr ⟨v⟩)
    have hf2 : (1:ℝ) / 2 ≤ f := by linarith
    have := mul_le_mul hf2 hr (by norm_num) hf
    linarith [hgq v]
  have hgne : g ≠ 0 := hg.ne'
  have hP0 : 0 ≤ ∏ v, q v ^ k := Finset.prod_nonneg (fun v _ => pow_nonneg (hqpos v).le k)
  have hinv0 : ∀ v, 0 ≤ 1 / q v := fun v => le_of_lt (one_div_pos.mpr (hqpos v))
  have hinv1 : ∀ v, 1 / q v ≤ 1 := fun v => by
    have := one_div_le_one_div_of_le one_pos (hq1 v)
    rwa [div_one] at this
  have hsum_inv : ∑ v, 1 / q v ≤ 2 * f / g := by
    calc ∑ v, 1 / q v ≤ ∑ _v : Pv, 1 / g :=
          Finset.sum_le_sum (fun v _ => one_div_le_one_div_of_le hg (hgq v))
      _ = 2 * f / g := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
  constructor
  · have hprod1 : 1 - ∑ v, 1 / q v ≤ ∏ v, (1 - 1 / q v) :=
      one_sub_sum_le_prod Finset.univ (fun v => 1 / q v) (fun v _ => hinv0 v) (fun v _ => hinv1 v)
    have hlow : ∏ v, (q v ^ k * (1 - 1 / q v)) ≤ ∏ v, nn v :=
      Finset.prod_le_prod (fun v _ => mul_nonneg (pow_nonneg (hqpos v).le k) (sub_nonneg.2 (hinv1 v)))
        (fun v _ => (hb v).1)
    rw [Finset.prod_mul_distrib] at hlow
    have h8 : 8 * f * r / g - 2 * f / g = (8 * f * r - 2 * f) / g := by rw [sub_div]
    have h8' : 0 ≤ (8 * f * r - 2 * f) / g := div_nonneg (by nlinarith) hg.le
    have hcoef : 1 - 8 * f * r / g ≤ ∏ v, (1 - 1 / q v) := by linarith
    calc (1 - 8 * f * r / g) * ∏ v, q v ^ k ≤ (∏ v, (1 - 1 / q v)) * ∏ v, q v ^ k :=
          mul_le_mul_of_nonneg_right hcoef hP0
      _ = (∏ v, q v ^ k) * ∏ v, (1 - 1 / q v) := by ring
      _ ≤ ∏ v, nn v := hlow
  · have ha0 : ∀ v, 0 ≤ (2 * r - 1) / q v := fun v => div_nonneg (by linarith) (hqpos v).le
    have hup : ∏ v, nn v ≤ ∏ v, (q v ^ k * (1 + (2 * r - 1) / q v)) :=
      Finset.prod_le_prod
        (fun v _ => le_trans (mul_nonneg (pow_nonneg (hqpos v).le k) (sub_nonneg.2 (hinv1 v))) (hb v).1)
        (fun v _ => (hb v).2)
    rw [Finset.prod_mul_distrib] at hup
    have hexp1 : ∏ v, (1 + (2 * r - 1) / q v) ≤ Real.exp (∑ v, (2 * r - 1) / q v) := by
      rw [Real.exp_sum]
      exact Finset.prod_le_prod (fun v _ => by linarith [ha0 v])
        (fun v _ => by linarith [Real.add_one_le_exp ((2 * r - 1) / q v)])
    have hsum_a : ∑ v, (2 * r - 1) / q v ≤ 4 * f * r / g := by
      have e : ∑ v, (2 * r - 1) / q v = (2 * r - 1) * ∑ v, 1 / q v := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun v _ => by ring)
      rw [e]
      have h2r : 0 ≤ 2 * r - 1 := by linarith
      have e2 : 4 * f * r / g - (2 * r - 1) * (2 * f / g) = 2 * f / g := by ring
      have e3 : 0 ≤ 2 * f / g := div_nonneg (by linarith) hg.le
      nlinarith [mul_le_mul_of_nonneg_left hsum_inv h2r]
    have hfr : 0 ≤ 4 * f * r := by
      have := mul_nonneg hf (by linarith : (0:ℝ) ≤ r); linarith
    have hT0 : 0 ≤ 4 * f * r / g := div_nonneg hfr hg.le
    have hT1 : 4 * f * r / g ≤ 1 := by
      have e4 : (g - 4 * f * r) / g = 1 - 4 * f * r / g := by rw [sub_div, div_self hgne]
      have e5 : 0 ≤ (g - 4 * f * r) / g := div_nonneg (by linarith) hg.le
      linarith
    have hexp2 : Real.exp (4 * f * r / g) ≤ 1 + 2 * (4 * f * r / g) := by
      have hc := convexOn_exp.2 (Set.mem_univ (1:ℝ)) (Set.mem_univ (0:ℝ)) hT0 (sub_nonneg.2 hT1)
        (by ring)
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero, Real.exp_zero] at hc
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      nlinarith
    have hprod : ∏ v, (1 + (2 * r - 1) / q v) ≤ 1 + 8 * f * r / g := by
      calc _ ≤ Real.exp (∑ v, (2 * r - 1) / q v) := hexp1
        _ ≤ Real.exp (4 * f * r / g) := Real.exp_le_exp.mpr hsum_a
        _ ≤ 1 + 2 * (4 * f * r / g) := hexp2
        _ = 1 + 8 * f * r / g := by ring
    calc ∏ v, nn v ≤ (∏ v, q v ^ k) * ∏ v, (1 + (2 * r - 1) / q v) := hup
      _ ≤ (∏ v, q v ^ k) * (1 + 8 * f * r / g) := mul_le_mul_of_nonneg_left hprod hP0
      _ = (1 + 8 * f * r / g) * ∏ v, q v ^ k := by ring
end Formalism.BranchingDeterminantCap
