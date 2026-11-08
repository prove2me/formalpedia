-- Prove2me | solution 1 for FocusSetRB.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:35:01.805204+00:00
-- url     : https://prove2.me/submissions/f7d674f6-6377-4aab-9b1a-d4368baa3df4

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_piBar

open Matrix

open FocusSetRB in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    (v : S → ℝ) (hv0 : ∀ s, 0 ≤ v s) (hv1 : ∑ s, v s = 1) :
    ∑ s, |((v - muStar y) ᵥ* Ppi M y) s| ≤ ∑ s, |v s - muStar y s| := by
  have hy0 : ∀ s a, 0 ≤ y s a := hy.1.2.2.2
  have hpi0 : ∀ s a, 0 ≤ piBar y s a := by
    intro s a
    unfold piBar
    split_ifs with h
    · exact div_nonneg (hy0 s a) h.le
    · norm_num
  have hpi1 : ∀ s, ∑ a, piBar y s a = 1 := by
    intro s
    rw [Fintype.sum_bool]
    unfold piBar
    split_ifs with h
    · rw [← add_div, div_eq_one_iff_eq h.ne']; ring
    · norm_num
  have hnn : ∀ s s', 0 ≤ Ppi M y s s' := by
    intro s s'
    simp only [Ppi, Matrix.of_apply]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hpi0 s a) (M.P_nonneg s a s'))
  have hrow : ∀ s, ∑ s', Ppi M y s s' = 1 := by
    intro s
    simp only [Ppi, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, M.P_sum_one, mul_one]
    exact hpi1 s
  calc ∑ s, |((v - muStar y) ᵥ* Ppi M y) s|
      = ∑ s, |∑ s', (v s' - muStar y s') * Ppi M y s' s| := by
        simp only [Matrix.vecMul, dotProduct, Pi.sub_apply]
    _ ≤ ∑ s, ∑ s', |v s' - muStar y s'| * Ppi M y s' s := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        refine (Finset.abs_sum_le_sum_abs (fun s' => (v s' - muStar y s') * Ppi M y s' s) Finset.univ).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        rw [abs_mul, abs_of_nonneg (hnn s' s)]
    _ = ∑ s', |v s' - muStar y s'| * ∑ s, Ppi M y s' s := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ∑ s, |v s - muStar y s| := by
        simp only [hrow, mul_one]
