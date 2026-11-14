-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:19.842749+00:00
-- url     : https://prove2.me/submissions/e5c81551-b0f1-449a-8c0c-ab3442b2f6f9

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem solution {j c : Fin (W.lastStage + 1)} (hjc : j ≤ c) :
    4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c ≤ 4 * W.pairValue j 0 c (1 / 2) := by
  have hR := W.arrivals_mono hjc
  have h1 := W.objective.diminishing_returns hR (W.candidate c)
  have h2 := W.objective.diminishing_returns
    (Finset.union_subset_union_left hR : W.arrivals j ∪ W.candidate 0 ⊆
      W.arrivals c ∪ W.candidate 0) (W.candidate c)
  have h3 := W.objective.monotone (W.arrivals c ∪ W.candidate c)
    ((W.arrivals c ∪ W.candidate 0) ∪ W.candidate c) (by
      intro e he
      simp only [Finset.mem_union] at he ⊢
      tauto)
  have hassoc : (W.arrivals j ∪ W.candidate 0) ∪ W.candidate c =
      W.arrivals j ∪ (W.candidate 0 ∪ W.candidate c) := Finset.union_assoc _ _ _
  rw [hassoc] at h2
  have hcomm : W.benchmark c = W.objective.value (W.arrivals c ∪ W.candidate c) := by
    rw [ConsistentSubmodular.WindowInstance.benchmark, Finset.union_comm]
  unfold ConsistentSubmodular.WindowInstance.credit ConsistentSubmodular.WindowInstance.gain ConsistentSubmodular.WindowInstance.residual ConsistentSubmodular.WindowInstance.arrivalValue ConsistentSubmodular.WindowInstance.pairValue ConsistentSubmodular.twoTypeValue
  rw [hcomm]
  nlinarith

end
