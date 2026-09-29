-- Prove2me | solution 1 for Devaney.sigma2_dist_agree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:08:03.737746+00:00
-- url     : https://prove2.me/submissions/880d1f1d-bb77-4944-a667-8009256c659c

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney Devaney.Sigma2

theorem dist_eq (s t : Sigma2) : dist s t = ∑' i, distTerm s t i := rfl

theorem entry_ne (s t : Sigma2) (i : ℕ) (h : s i ≠ t i) : s.entry i ≠ t.entry i := fun he =>
  h (Fin.ext (Nat.cast_injective he))

theorem distTerm_eq_zero (s t : Sigma2) (i : ℕ) (h : s i = t i) : distTerm s t i = 0 := by
  simp [distTerm, entry, h]

theorem distTerm_eq_of_ne (s t : Sigma2) (i : ℕ) (h : s i ≠ t i) :
    distTerm s t i = 1 / 2 ^ i := by
  have hne := entry_ne s t i h
  have h1 : |s.entry i - t.entry i| = 1 := by
    rcases entry_mem s i with hs | hs <;> rcases entry_mem t i with ht | ht
    · exact absurd (hs.trans ht.symm) hne
    · rw [hs, ht]; norm_num
    · rw [hs, ht]; norm_num
    · exact absurd (hs.trans ht.symm) hne
  rw [distTerm, h1]

/-- The tail of the defining series past index `n` is at most `1 / 2 ^ n`. -/
theorem tail_le (s t : Sigma2) (n : ℕ) :
    ∑' i, distTerm s t (i + (n + 1)) ≤ 1 / 2 ^ n := by
  have hsummable : Summable (fun i => distTerm s t (i + (n + 1))) :=
    (summable_distTerm s t).comp_injective (add_left_injective (n + 1))
  have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + (n + 1))) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_right ((1/2 : ℝ) ^ (n + 1))
  calc ∑' i, distTerm s t (i + (n + 1))
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (n + 1)) :=
        Summable.tsum_le_tsum (fun i => distTerm_le s t _) hsummable hg
    _ = 1 / 2 ^ n := by
        rw [show (fun i : ℕ => (1/2:ℝ) ^ (i + (n+1))) = fun i : ℕ => (1/2:ℝ) ^ (n+1) * (1/2)^i from
          by funext i; rw [pow_add, mul_comm]]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        rw [pow_succ]
        norm_num
        rw [← inv_pow]
        ring

/-- Proposition 6.3. -/
theorem sigma2_dist_agree (s t : Sigma2) (n : ℕ) :
    ((∀ i ≤ n, s i = t i) → dist s t ≤ 1 / 2 ^ n) ∧
      (dist s t < 1 / 2 ^ n → ∀ i ≤ n, s i = t i) := by
  constructor
  · intro h
    have hsplit := (summable_distTerm s t).sum_add_tsum_nat_add (n + 1)
    have hzero : ∑ i ∈ Finset.range (n + 1), distTerm s t i = 0 :=
      Finset.sum_eq_zero fun i hi =>
        distTerm_eq_zero s t i (h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    rw [hzero, zero_add] at hsplit
    rw [dist_eq, ← hsplit]
    exact tail_le s t n
  · intro hlt i hi
    by_contra hne
    have h1 : distTerm s t i = 1 / 2 ^ i := distTerm_eq_of_ne s t i hne
    have h2 : distTerm s t i ≤ ∑' j, distTerm s t j :=
      (summable_distTerm s t).le_tsum i fun j _ => distTerm_nonneg s t j
    have h3 : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ i := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hi
    rw [dist_eq] at hlt
    rw [h1] at h2
    linarith

end DevFix

open Devaney Devaney.Sigma2 in
theorem solution (s t : Sigma2) (n : ℕ) :
    ((∀ i ≤ n, s i = t i) → dist s t ≤ 1 / 2 ^ n) ∧
      (dist s t < 1 / 2 ^ n → ∀ i ≤ n, s i = t i) :=
  DevFix.sigma2_dist_agree s t n
