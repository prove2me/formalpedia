-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.value_le_before
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:06.266039+00:00
-- url     : https://prove2.me/submissions/a1a5ee0d-d113-426d-b2c5-47707c779ede

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream
import Theorems.Thm_ConsistentSubmodular_HardInstance_card_fiber_le_tinyCount

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance
variable {k : ℕ} {u : Fin 3 → ℝ}

theorem solution (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2)))
    (hS : ∀ e ∈ S, e.val < 3 * k) :
    weightedValue k u S ≤
      u 0 * tinyCount k 0 S + u 1 * tinyCount k 1 S + u 2 * tinyCount k 2 S := by
  rw [weightedValue, Fin.sum_univ_three]
  have h0 : ((fiber (S.biUnion (elementCells k)) 0).card : ℝ) ≤ tinyCount k 0 S := by
    exact_mod_cast card_fiber_le_tinyCount S 0 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 0
      omega
  have h1 : ((fiber (S.biUnion (elementCells k)) 1).card : ℝ) ≤ tinyCount k 1 S := by
    exact_mod_cast card_fiber_le_tinyCount S 1 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 1
      omega
  have h2 : ((fiber (S.biUnion (elementCells k)) 2).card : ℝ) ≤ tinyCount k 2 S := by
    exact_mod_cast card_fiber_le_tinyCount S 2 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 2
      omega
  have := mul_le_mul_of_nonneg_left h0 (hu 0)
  have := mul_le_mul_of_nonneg_left h1 (hu 1)
  have := mul_le_mul_of_nonneg_left h2 (hu 2)
  linarith

end
