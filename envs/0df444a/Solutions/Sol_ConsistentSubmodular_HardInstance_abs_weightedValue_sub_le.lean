-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.abs_weightedValue_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:52.355759+00:00
-- url     : https://prove2.me/submissions/e2032d61-dfc4-4346-9445-36200e0a0e7e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

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

theorem solution {v : Fin 3 → ℝ} {δ : ℝ} (h0 : v 0 = u 0)
    (h1 : |v 1 - u 1| ≤ δ) (h2 : |v 2 - u 2| ≤ δ) (T : Finset (Fin (3 * k + 2))) :
    |weightedValue k v T - weightedValue k u T| ≤ 2 * δ * k := by
  have hc₁ : ((fiber (T.biUnion (elementCells k)) 1).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (T.biUnion (elementCells k)) 1
  have hc₂ : ((fiber (T.biUnion (elementCells k)) 2).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (T.biUnion (elementCells k)) 2
  set c₁ : ℝ := ((fiber (T.biUnion (elementCells k)) 1).card : ℝ)
  set c₂ : ℝ := ((fiber (T.biUnion (elementCells k)) 2).card : ℝ)
  have hdiff : weightedValue k v T - weightedValue k u T = (v 1 - u 1) * c₁ + (v 2 - u 2) * c₂ := by
    simp only [weightedValue, Fin.sum_univ_three, h0, c₁, c₂]
    ring
  have hc₁0 : 0 ≤ c₁ := Nat.cast_nonneg _
  have hc₂0 : 0 ≤ c₂ := Nat.cast_nonneg _
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h1
  rw [hdiff]
  calc |(v 1 - u 1) * c₁ + (v 2 - u 2) * c₂|
      ≤ |(v 1 - u 1) * c₁| + |(v 2 - u 2) * c₂| := abs_add_le _ _
    _ = |v 1 - u 1| * c₁ + |v 2 - u 2| * c₂ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc₁0, abs_of_nonneg hc₂0]
    _ ≤ δ * k + δ * k :=
        add_le_add (mul_le_mul h1 hc₁ hc₁0 hδ) (mul_le_mul h2 hc₂ hc₂0 hδ)
    _ = 2 * δ * k := by ring

end
