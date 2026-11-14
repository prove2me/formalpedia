-- Prove2me | solution 1 for ConsistentSubmodular.Objective.optimum_thinning
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:17.487578+00:00
-- url     : https://prove2.me/submissions/bd4ceb71-29d5-45de-b686-591e34df3a48

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Theorems.Thm_ConsistentSubmodular_Objective_exists_thinned_subset

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (N : Finset (Fin n)) {r k : ℕ} (hrk : r ≤ k) :
    (r : ℝ) * f.bufferedOptimum N ∅ k ≤
      (k : ℝ) * f.bufferedOptimum N ∅ r := by
  let A := f.bufferedOptimizer N ∅ k
  have hA := f.bufferedOptimizer_spec N ∅ k
  by_cases hAr : A.card ≤ r
  · have hArval : f.bufferedOptimum N ∅ k ≤ f.bufferedOptimum N ∅ r := by
      simpa [bufferedOptimum, A] using f.le_bufferedOptimum (Q := ∅) hA.1 hAr
    exact (mul_le_mul_of_nonneg_left hArval (Nat.cast_nonneg r)).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hrk) (f.bufferedOptimum_nonnegative N ∅ r))
  · have hrA : r ≤ A.card := by omega
    obtain ⟨B, hBA, hBr, hBval⟩ := f.exists_thinned_subset A r hrA
    have hBopt : f.value B ≤ f.bufferedOptimum N ∅ r := by
      simpa using f.le_bufferedOptimum (Q := ∅) (hBA.trans hA.1) hBr.le
    have hAk : A.card ≤ k := hA.2.1
    have h1 := mul_le_mul_of_nonneg_left hBopt (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    have h2 := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hAk : (A.card : ℝ) ≤ k)
      (f.bufferedOptimum_nonnegative N ∅ r)
    simpa [bufferedOptimum, A] using hBval.trans (h1.trans h2)

end
