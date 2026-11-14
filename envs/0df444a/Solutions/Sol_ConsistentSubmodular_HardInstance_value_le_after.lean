-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.value_le_after
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:07.739653+00:00
-- url     : https://prove2.me/submissions/25dfbc32-f3c8-4d7d-8ea8-1bd7433692cc

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream
import Theorems.Thm_ConsistentSubmodular_HardInstance_card_fiber_le_tinyCount

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- A fibre has at most `k` cells. -/
theorem card_fiber_le {k : ℕ} (C : Finset (Fin 3 × Fin k)) (g : Fin 3) :
    (fiber C g).card ≤ k := by
  calc (fiber C g).card ≤ (univ : Finset (Fin k)).card := by
        refine card_le_card_of_injOn Prod.snd (fun _ _ => mem_univ _) ?_
        intro c hc c' hc' h
        have h1 := (mem_filter.mp (mem_coe.mp hc)).2
        have h2 := (mem_filter.mp (mem_coe.mp hc')).2
        exact Prod.ext (h1.trans h2.symm) h
    _ = k := by simp

end ConsistentSubmodular.HardInstance

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance
variable {k : ℕ} {u : Fin 3 → ℝ}

theorem solution (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2))) :
    weightedValue k u S ≤ u 0 * k + u 1 * k + u 2 * tinyCount k 2 S := by
  rw [weightedValue, Fin.sum_univ_three]
  have h0 : ((fiber (S.biUnion (elementCells k)) 0).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (S.biUnion (elementCells k)) 0
  have h1 : ((fiber (S.biUnion (elementCells k)) 1).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (S.biUnion (elementCells k)) 1
  have h2 : ((fiber (S.biUnion (elementCells k)) 2).card : ℝ) ≤ tinyCount k 2 S := by
    exact_mod_cast card_fiber_le_tinyCount S 2 fun e he => by
      have := e.isLt
      change e.val ≠ 3 * k + 2
      omega
  have := mul_le_mul_of_nonneg_left h0 (hu 0)
  have := mul_le_mul_of_nonneg_left h1 (hu 1)
  have := mul_le_mul_of_nonneg_left h2 (hu 2)
  linarith

end
