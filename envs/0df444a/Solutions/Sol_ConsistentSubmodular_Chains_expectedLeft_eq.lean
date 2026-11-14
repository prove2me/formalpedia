-- Prove2me | solution 1 for ConsistentSubmodular.Chains.expectedLeft_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:28.38296+00:00
-- url     : https://prove2.me/submissions/be84a39a-4378-430e-82a4-392a1fe436b6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution
import Theorems.Thm_ConsistentSubmodular_Chains_isEqualizing_iff
import Theorems.Thm_ConsistentSubmodular_Chains_left_eq_sum

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem sum_Iic_eq {N : ℕ} (f : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i, if i ≤ j then f i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)

include hI

theorem length_antitone : Antitone (intervalLength I) :=
  Fin.antitone_iff_succ_le.mpr fun i => hI.2.2.1 i

theorem length_pos (j : Fin (N + 1)) : 0 < intervalLength I j :=
  lt_of_lt_of_le hI.2.2.2 (length_antitone hI (Fin.le_last j))

end Consecutive

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

section Equalizing

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)

include hI hE

/-- The cumulative probabilities (5) of the equalizing distribution. -/
theorem cumulative_prob (i : Fin (N + 1)) :
    ∑ j ∈ Finset.Iic i, I.prob j = intervalLength I (Fin.last N) / intervalLength I i :=
  (isEqualizing_iff hI).mp hE i

end Equalizing

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)
include hI hE

theorem solution : ∑ j, I.prob j * I.left j =
    ∑ j : Fin N, (intervalLength I j.castSucc - intervalLength I (Fin.last N)) := by
  have htail : ∀ i : Fin (N + 1), ∑ j, (if i < j then I.prob j else 0) =
      1 - intervalLength I (Fin.last N) / intervalLength I i := by
    intro i
    have h : ∑ j ∈ Finset.Iic i, I.prob j =
        intervalLength I (Fin.last N) / intervalLength I i := cumulative_prob hI hE i
    rw [← h, sum_Iic_eq, ← I.prob_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ≤ i
    · rw [if_neg (not_lt.mpr h), if_pos h, sub_self]
    · rw [if_pos (lt_of_not_ge h), if_neg h, sub_zero]
  calc ∑ j, I.prob j * I.left j
      = ∑ j, ∑ i, (if i < j then I.prob j * intervalLength I i else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [left_eq_sum hI j, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
    _ = ∑ i, intervalLength I i * ∑ j, (if i < j then I.prob j else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
    _ = ∑ i, (intervalLength I i - intervalLength I (Fin.last N)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [htail i]
        have := (length_pos hI i).ne'
        field_simp
    _ = ∑ j : Fin N, (intervalLength I j.castSucc - intervalLength I (Fin.last N)) := by
        rw [Fin.sum_univ_castSucc, sub_self, add_zero]

end
