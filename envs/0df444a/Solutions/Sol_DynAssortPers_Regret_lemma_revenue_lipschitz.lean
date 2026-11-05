-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_revenue_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:53:16.272+00:00
-- url     : https://prove2.me/submissions/5fbb62da-5313-4f66-875c-3e4b9399375a

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL
import Theorems.Thm_DynAssortPers_Regret_lemma_choice_prob_lipschitz

open DynAssortPers.Regret

namespace DAPrev

lemma revenue_eq {n : ℕ} (S : Finset (Fin n)) (w θ : Fin n → ℝ) :
    revenue S w θ = ∑ j ∈ S, w j * choiceProb θ S j := by
  unfold revenue ChoiceCDLP.MNL.mnlObjective
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [choiceProb, if_pos hj]
  rw [add_comm (∑ j ∈ S, Real.exp (θ j)) 1]
  ring

lemma le_supNorm {n : ℕ} (w : Fin n → ℝ) (j : Fin n) : |w j| ≤ supNorm w :=
  le_ciSup (f := fun j => |w j|) (Finite.bddAbove_range _) j

lemma supNorm_nonneg {n : ℕ} (w : Fin n → ℝ) : 0 ≤ supNorm w :=
  Real.iSup_nonneg (fun j => abs_nonneg (w j))

lemma rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

lemma card_mul_sqrt_le {n : ℕ} (S : Finset (Fin n)) (K : ℕ) (hS : S.card ≤ K) :
    (S.card : ℝ) * Real.sqrt (S.card : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [rpow_three_halves _ (by positivity)]
  have h : (S.card : ℝ) ≤ K := by exact_mod_cast hS
  exact mul_le_mul h (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) (by positivity)

lemma revenue_diff_le {n : ℕ} (S : Finset (Fin n)) (w θ θ' : Fin n → ℝ) :
    |revenue S w θ - revenue S w θ'| ≤
      ∑ j ∈ S, supNorm w * |choiceProb θ S j - choiceProb θ' S j| := by
  rw [revenue_eq, revenue_eq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (le_supNorm w j) (abs_nonneg _)

theorem rev_lip {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ K)
    (w θ θ' : Fin n → ℝ) :
    |revenue S w θ - revenue S w θ'| ≤
      (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' := by
  refine (revenue_diff_le S w θ θ').trans ?_
  have h1 : ∑ j ∈ S, supNorm w * |choiceProb θ S j - choiceProb θ' S j| ≤
      ∑ j ∈ S, supNorm w * ((1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ') :=
    Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (lemma_choice_prob_lipschitz S j hj θ θ') (supNorm_nonneg w))
  refine h1.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hd : 0 ≤ euclidDist θ θ' := by unfold euclidDist; positivity
  have := card_mul_sqrt_le S K hS
  have hw := supNorm_nonneg w
  calc (S.card : ℝ) * (supNorm w * (1 / 4 * Real.sqrt (S.card : ℝ) * euclidDist θ θ'))
      = (1 / 4) * supNorm w * ((S.card : ℝ) * Real.sqrt (S.card : ℝ)) * euclidDist θ θ' := by ring
    _ ≤ _ := by gcongr

end DAPrev

theorem solution {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ K)
    (w θ θ' : Fin n → ℝ) :
    |revenue S w θ - revenue S w θ'| ≤
      (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' :=
  DAPrev.rev_lip K S hS w θ θ'
