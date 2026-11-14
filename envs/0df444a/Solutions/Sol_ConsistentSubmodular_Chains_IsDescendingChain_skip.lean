-- Prove2me | solution 1 for ConsistentSubmodular.Chains.IsDescendingChain.skip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:34.729906+00:00
-- url     : https://prove2.me/submissions/8bc77fa7-ea9e-425f-9983-0953269648f0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

namespace IsDescendingChain

variable {x y z : ℝ} {rest : List ℝ}

theorem le_head (h : IsDescendingChain (x :: y :: rest)) : y ≤ x :=
  (List.isChain_cons_cons.mp h.1).1

theorem tail (h : IsDescendingChain (x :: y :: rest)) : IsDescendingChain (y :: rest) :=
  ⟨(List.isChain_cons_cons.mp h.1).2, fun w hw => h.2.1 w (List.mem_cons_of_mem x hw),
    by rw [← List.getLast?_cons_cons (a := x)]; exact h.2.2⟩

end IsDescendingChain

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
open ConsistentSubmodular.Chains.IsDescendingChain
variable {x y z : ℝ} {rest : List ℝ}

theorem solution (h : IsDescendingChain (x :: y :: z :: rest)) : IsDescendingChain (x :: z :: rest) := by
  have hyx := h.le_head
  have hzy := h.tail.le_head
  refine ⟨List.isChain_cons_cons.mpr ⟨hzy.trans hyx, (List.isChain_cons_cons.mp h.1).2.tail⟩, ?_, ?_⟩
  · intro w hw
    apply h.2.1
    simp only [List.mem_cons] at hw ⊢
    tauto
  · rw [List.getLast?_cons_cons]
    have h2 := h.2.2
    rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at h2
    exact h2

end
