-- Prove2me | solution 1 for ConsistentSubmodular.Chains.adaptivityGap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:27.844439+00:00
-- url     : https://prove2.me/submissions/28d8027c-3d5c-4b20-b182-1407278945f1

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution
import Theorems.Thm_ConsistentSubmodular_Chains_right_le_left
import Theorems.Thm_ConsistentSubmodular_Chains_isEqualizing_iff

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

theorem left_monotone : Monotone I.left := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  rw [hI.2.1 i]
  exact I.left_le_right i.castSucc

/-- Interval `i` contributes `d_i` at realizations `j ≤ i` and nothing at `j > i`. -/
theorem value_eq (i j : Fin (N + 1)) :
    I.value i j = I.left j + if j ≤ i then intervalLength I i else 0 := by
  unfold IntervalInstance.value intervalLength
  split_ifs with hji
  · rw [max_eq_left (left_monotone hI hji),
      max_eq_right (sub_nonneg.mpr (I.left_le_right i))]
  · have hij : i < j := lt_of_not_ge hji
    have h1 := right_le_left hI hij
    rw [max_eq_right (left_monotone hI hij.le), max_eq_left (by linarith), add_zero]

/-- Every fixed interval `i` has expected value `E[ℓ_j] + d_i Σ_{j ≤ i} p_j`. -/
theorem expectedValue_eq_cumulative (i : Fin (N + 1)) :
    ∑ j, I.prob j * I.value i j =
      ∑ j, I.prob j * I.left j + intervalLength I i * ∑ j ∈ Finset.Iic i, I.prob j := by
  simp_rw [value_eq hI, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [sum_Iic_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

end Consecutive

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)

include hI

/-- Interval `j` is a best interval in hindsight for realization `j`: earlier
intervals have no surviving length, and later intervals have length at most `d_j`. -/
theorem maxValue_eq (j : Fin (N + 1)) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => I.value i j) =
      I.left j + intervalLength I j := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [value_eq hI]
    split_ifs with h
    · linarith [length_antitone hI h]
    · linarith [length_pos hI j]
  · apply Finset.le_sup'_of_le _ (Finset.mem_univ j)
    rw [value_eq hI, if_pos le_rfl]

/-- `C = E[d_j] ≥ d_N`. -/
theorem length_last_le_expectedLength :
    intervalLength I (Fin.last N) ≤ ∑ j, I.prob j * intervalLength I j := by
  calc intervalLength I (Fin.last N) = ∑ j, I.prob j * intervalLength I (Fin.last N) := by
        rw [← Finset.sum_mul, I.prob_sum, one_mul]
    _ ≤ ∑ j, I.prob j * intervalLength I j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (length_antitone hI (Fin.le_last j)) (I.prob_nonneg j)

end Consecutive

section Equalizing

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)

include hI hE

/-- The cumulative probabilities (5) of the equalizing distribution. -/
theorem cumulative_prob (i : Fin (N + 1)) :
    ∑ j ∈ Finset.Iic i, I.prob j = intervalLength I (Fin.last N) / intervalLength I i :=
  (isEqualizing_iff hI).mp hE i

/-- Every fixed interval has expected value `E[ℓ_j] + d_N`. -/
theorem expectedValue_eq (i : Fin (N + 1)) :
    ∑ j, I.prob j * I.value i j = ∑ j, I.prob j * I.left j + intervalLength I (Fin.last N) := by
  rw [expectedValue_eq_cumulative hI, cumulative_prob hI hE i, mul_div_assoc',
    mul_div_cancel_left₀ _ (length_pos hI i).ne']

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

theorem solution : I.adaptivityGap =
    (∑ j, I.prob j * I.left j + intervalLength I (Fin.last N)) /
      (∑ j, I.prob j * I.left j + ∑ j, I.prob j * intervalLength I j) := by
  have hfix : I.fixedValue = ∑ j, I.prob j * I.left j + intervalLength I (Fin.last N) := by
    unfold IntervalInstance.fixedValue
    simp_rw [expectedValue_eq hI hE]
    exact Finset.sup'_const _ _
  have hada : I.adaptiveValue = ∑ j, I.prob j * I.left j + ∑ j, I.prob j * intervalLength I j := by
    unfold IntervalInstance.adaptiveValue
    simp_rw [maxValue_eq hI, mul_add, Finset.sum_add_distrib]
  have hB : 0 ≤ ∑ j, I.prob j * I.left j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (I.prob_nonneg j) (I.left_nonneg j)
  have hC := length_last_le_expectedLength hI
  have hpos : 0 < I.adaptiveValue := by
    rw [hada]
    linarith [length_pos hI (Fin.last N)]
  unfold IntervalInstance.adaptivityGap
  rw [if_neg hpos.ne', hfix, hada]

end
