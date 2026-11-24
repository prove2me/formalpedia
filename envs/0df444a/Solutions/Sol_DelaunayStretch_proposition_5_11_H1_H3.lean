-- Prove2me | solution 1 for DelaunayStretch.proposition_5_11_H1_H3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:14:53.994968+00:00
-- url     : https://prove2.me/submissions/2c27b7f6-2d63-43e6-b028-cadea2d0fcd1

import Theorems.Thm_DelaunayStretch_lemma_5_8_reduction_H1
import Theorems.Thm_DelaunayStretch_lemma_5_9_reduction_H2
import Theorems.Thm_DelaunayStretch_lemma_5_10_reduction_H3
import Theorems.Thm_DelaunayStretch_check_5_11_a_R_bound
import Theorems.Thm_DelaunayStretch_check_5_11_b_H1_inequalities
import Theorems.Thm_DelaunayStretch_check_5_11_c_monotonicity
import Theorems.Thm_DelaunayStretch_check_5_11_d_H3_inequality

open DelaunayStretch

theorem hstarV_rev (i j : Fin 12) (l : Fin 35) :
    hstarV (Fin.rev i) (Fin.rev j) l = -hstarV i j l := by
  have hi := i.isLt; have hj := j.isLt
  have ri : ((Fin.rev i : Fin 12) : ℕ) = 11 - i := by simp [Fin.val_rev]
  have rj : ((Fin.rev j : Fin 12) : ℕ) = 11 - j := by simp [Fin.val_rev]
  unfold hstarV
  rw [ri, rj]
  by_cases h : (i : ℕ) ≤ 5
  · rw [if_neg (show ¬ (11 - (i : ℕ) ≤ 5) by omega), if_pos h,
      show 11 - (11 - (i : ℕ)) = i by omega, show 11 - (11 - (j : ℕ)) = j by omega]
  · rw [if_pos (show 11 - (i : ℕ) ≤ 5 by omega), if_neg h, neg_neg]

theorem hstarR_rev (i j : Fin 6) (l : Fin 35) :
    hstarR (Fin.rev i) (Fin.rev j) l = hstarR i j l := by
  have hi := i.isLt; have hj := j.isLt
  have ri : ((Fin.rev i : Fin 6) : ℕ) = 5 - i := by simp [Fin.val_rev]
  have rj : ((Fin.rev j : Fin 6) : ℕ) = 5 - j := by simp [Fin.val_rev]
  unfold hstarR
  rw [ri, rj]
  by_cases h : 6 * (i : ℕ) + j ≤ 17
  · rw [if_neg (show ¬ (6 * (5 - (i : ℕ)) + (5 - (j : ℕ)) ≤ 17) by omega), if_pos h,
      show 5 - (5 - (i : ℕ)) = i by omega, show 5 - (5 - (j : ℕ)) = j by omega]
  · rw [if_pos (show 6 * (5 - (i : ℕ)) + (5 - (j : ℕ)) ≤ 17 by omega), if_neg h]

theorem hstar_coeff_conditions : FamilyCoeffConditions hstarV hstarR hstarB hstarD := by
  refine ⟨hstarV_rev, hstarR_rev, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel


theorem solution :
    CondH1 Hstar ∧ CondH3 (159485994 / 100000000 : ℝ) Hstar ∧
      ∀ z g : R4, IsPieceGradient hstarV hstarR hstarB hstarD z g → |g.2.1| ≤ g.2.2.1 := by
  have h2 := lemma_5_9_reduction_H2 hstarV hstarR hstarB hstarD check_5_11_c_monotonicity
  refine ⟨?_, ?_, h2⟩
  · exact lemma_5_8_reduction_H1 hstarV hstarR hstarB hstarD (1 / 50) (by norm_num)
      check_5_11_a_R_bound check_5_11_b_H1_inequalities
  · exact lemma_5_10_reduction_H3 hstarV hstarR hstarB hstarD hstar_coeff_conditions _ h2
      check_5_11_d_H3_inequality
