-- Prove2me | solution 1 for BlockCycleRotation.weighted_geom_sum_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:17:11.811695+00:00
-- url     : https://prove2.me/submissions/d772c904-273c-4894-9934-37e532c67906

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {θ : ℝ} (hne : e θ ≠ 1) (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ((T - 1 : ℕ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)) / (e θ - 1):= by
  have key : ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j := by
    rw [Finset.sum_Ico_Ico_comm 1 T (fun _ j => e θ ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  have hx1 : e θ - 1 ≠ 0 := sub_ne_zero.2 hne
  have hinner : ∀ i ∈ Finset.Ico 1 T,
      ∑ j ∈ Finset.Ico i T, e θ ^ j = (e θ ^ T - e θ ^ i) / (e θ - 1) := by
    intro i hi
    exact geom_sum_Ico hne (Finset.mem_Ico.1 hi).2.le
  rw [key, Finset.sum_congr rfl hinner]
  have hsplit : ∑ i ∈ Finset.Ico 1 T, (e θ ^ T - e θ ^ i) / (e θ - 1)
      = ((∑ _i ∈ Finset.Ico 1 T, e θ ^ T) - ∑ i ∈ Finset.Ico 1 T, e θ ^ i) / (e θ - 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
  rw [hsplit, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, geom_sum_Ico hne hT]
  norm_num
