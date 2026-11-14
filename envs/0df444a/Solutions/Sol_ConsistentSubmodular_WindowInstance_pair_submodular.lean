-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.pair_submodular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:20.89645+00:00
-- url     : https://prove2.me/submissions/c58b20df-aa77-4c87-9314-7ec6c2e96569

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem solution (j a b : Fin (W.lastStage + 1)) :
    W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) +
        W.objective.value (W.arrivals j) ≤
      W.objective.value (W.arrivals j ∪ W.candidate a) +
        W.objective.value (W.arrivals j ∪ W.candidate b) := by
  have hs := W.objective.submodular (W.arrivals j ∪ W.candidate a) (W.arrivals j ∪ W.candidate b)
  have hu : (W.arrivals j ∪ W.candidate a) ∪ (W.arrivals j ∪ W.candidate b) =
      W.arrivals j ∪ (W.candidate a ∪ W.candidate b) := by
    ext e
    simp only [Finset.mem_union]
    tauto
  have hm := W.objective.monotone (W.arrivals j)
    ((W.arrivals j ∪ W.candidate a) ∩ (W.arrivals j ∪ W.candidate b))
    (Finset.subset_inter Finset.subset_union_left Finset.subset_union_left)
  rw [hu] at hs
  linarith

end
