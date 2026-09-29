-- Prove2me | solution 1 for BanditAlgorithm.bandit_moss_minimax_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-20T19:59:12.507407+00:00
-- url     : https://prove2.me/submissions/39d367b2-0fbe-4b9c-826e-3642aa391be0

import Theorems.Thm_BanditAlgorithm_moss_regret_intermediate_bound
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Source-faithful reduction of Lattimore and Szepesvari, *Bandit Algorithms*
(CUP 2020), Theorem 9.1, printed pp. 124--127 (PDF pp. 133--136).
The child is the stochastic intermediate estimate displayed across printed
pp. 126--127. This file performs only the source's final filtered-sum and
constant calculation.
-/

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

theorem solution {k : ℕ}
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditPolicy k} (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    banditRegret ν π n ≤
      39 * Real.sqrt ((k : ℝ) * n) + ∑ i, banditGap ν i := by
  classical
  by_cases hk0 : k = 0
  · subst k
    obtain ⟨a, -⟩ := hπ 0 (fun t ↦ Fin.elim0 t)
    exact Fin.elim0 a
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hcore := moss_regret_intermediate_bound hk hν hπ hkn
  let S : Finset (Fin k) := Finset.univ.filter
    (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i)
  have hgap (i : Fin k) : 0 ≤ banditGap ν i := by
    rw [banditGap, sub_nonneg]
    exact Finite.le_ciSup (fun j : Fin k ↦ banditArmMean ν j) i
  have hsum_gap : ∑ i ∈ S, banditGap ν i ≤ ∑ i, banditGap ν i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ ↦ hgap i)
  have hcard : (S.card : ℝ) ≤ k := by
    have hcard_nat : S.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    exact_mod_cast hcard_nat
  have hsqrt_ratio : 0 ≤ Real.sqrt ((n : ℝ) / k) := Real.sqrt_nonneg _
  have hscaled_card :
      (S.card : ℝ) * (15 * Real.sqrt ((n : ℝ) / k)) ≤
        (k : ℝ) * (15 * Real.sqrt ((n : ℝ) / k)) := by
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hk_real : (0 : ℝ) < k := by exact_mod_cast hk
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt_mul :
      (k : ℝ) * Real.sqrt ((n : ℝ) / k) = Real.sqrt ((k : ℝ) * n) := by
    calc
      (k : ℝ) * Real.sqrt ((n : ℝ) / k) =
          |(k : ℝ)| * Real.sqrt ((n : ℝ) / k) := by rw [abs_of_pos hk_real]
      _ = Real.sqrt ((k : ℝ) ^ 2) * Real.sqrt ((n : ℝ) / k) := by
        rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (((k : ℝ) ^ 2) * ((n : ℝ) / k)) := by
        rw [Real.sqrt_mul (sq_nonneg (k : ℝ))]
      _ = Real.sqrt ((k : ℝ) * n) := by
        congr 1
        field_simp
  have hfilter :
      ∑ i ∈ S, (banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) ≤
        ∑ i, banditGap ν i + 15 * Real.sqrt ((k : ℝ) * n) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      (∑ i ∈ S, banditGap ν i) +
            (S.card : ℝ) * (15 * Real.sqrt ((n : ℝ) / k)) ≤
          (∑ i, banditGap ν i) +
            (k : ℝ) * (15 * Real.sqrt ((n : ℝ) / k)) :=
        add_le_add hsum_gap hscaled_card
      _ = (∑ i, banditGap ν i) + 15 * Real.sqrt ((k : ℝ) * n) := by
        calc
          (∑ i, banditGap ν i) + (k : ℝ) * (15 * Real.sqrt ((n : ℝ) / k)) =
              (∑ i, banditGap ν i) + 15 * ((k : ℝ) * Real.sqrt ((n : ℝ) / k)) := by
                ring
          _ = (∑ i, banditGap ν i) + 15 * Real.sqrt ((k : ℝ) * n) := by
            rw [hsqrt_mul]
  change banditRegret ν π n ≤
    39 * Real.sqrt ((k : ℝ) * n) + ∑ i, banditGap ν i
  change banditRegret ν π n ≤
    24 * Real.sqrt ((k : ℝ) * n) +
      ∑ i ∈ S, (banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) at hcore
  linarith
