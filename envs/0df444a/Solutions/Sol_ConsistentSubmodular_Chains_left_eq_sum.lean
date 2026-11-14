-- Prove2me | solution 1 for ConsistentSubmodular.Chains.left_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:36.258937+00:00
-- url     : https://prove2.me/submissions/1aeee026-b9f9-4332-b44b-3637bf4ea906

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

theorem solution (j : Fin (N + 1)) :
    I.left j = ∑ i, if i < j then intervalLength I i else 0 := by
  induction j using Fin.induction with
  | zero =>
    rw [hI.1]
    symm
    exact Finset.sum_eq_zero fun i _ => if_neg (Fin.not_lt_zero i)
  | succ j ih =>
    rw [hI.2.1 j, show I.right j.castSucc = I.left j.castSucc + intervalLength I j.castSucc by
      unfold intervalLength; ring, ih]
    have h : ∀ i : Fin (N + 1), (if i < j.succ then intervalLength I i else 0) =
        (if i < j.castSucc then intervalLength I i else 0) +
          (if i = j.castSucc then intervalLength I i else 0) := by
      intro i
      have hlt : i < j.succ ↔ i < j.castSucc ∨ i = j.castSucc := by
        rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      by_cases h1 : i < j.castSucc
      · have h2 : i ≠ j.castSucc := ne_of_lt h1
        rw [if_pos (hlt.mpr (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
      · by_cases h2 : i = j.castSucc
        · rw [if_pos (hlt.mpr (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
        · rw [if_neg (fun h => (hlt.mp h).elim h1 h2), if_neg h1, if_neg h2, add_zero]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp

end
