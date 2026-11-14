-- Prove2me | solution 1 for ConsistentSubmodular.Chains.tail_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:08.862957+00:00
-- url     : https://prove2.me/submissions/69420c8c-be9a-47af-8158-0f1abe4daab0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Theorems.Thm_ConsistentSubmodular_Chains_collapse_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem chainValue_cons_cons (x y : ℝ) (rest : List ℝ) :
    chainValue (x :: y :: rest) = edgeValue x y + chainValue (y :: rest) := rfl

namespace IsDescendingChain

variable {x y z : ℝ} {rest : List ℝ}

theorem le_head (h : IsDescendingChain (x :: y :: rest)) : y ≤ x :=
  (List.isChain_cons_cons.mp h.1).1

theorem one_le {L : List ℝ} (h : IsDescendingChain L) {w : ℝ} (hw : w ∈ L) : 1 ≤ w :=
  h.2.1 w hw

theorem tail (h : IsDescendingChain (x :: y :: rest)) : IsDescendingChain (y :: rest) :=
  ⟨(List.isChain_cons_cons.mp h.1).2, fun w hw => h.2.1 w (List.mem_cons_of_mem x hw),
    by rw [← List.getLast?_cons_cons (a := x)]; exact h.2.2⟩

theorem eq_one_of_singleton (h : IsDescendingChain [x]) : x = 1 := by
  have h2 := h.2.2
  rw [List.getLast?_singleton] at h2
  exact Option.some.inj h2

end IsDescendingChain

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution (z : ℝ) (rest : List ℝ) (h : IsDescendingChain (z :: rest))
    (hzL : z ≤ collapseBound) : chainValue (z :: rest) ≤ edgeValue z 1 := by
  induction rest generalizing z with
  | nil =>
    rw [h.eq_one_of_singleton]
    simp [chainValue, edgeValue]
  | cons y rest ih =>
    have hyz := h.le_head
    have hy1 : 1 ≤ y := h.one_le (by simp)
    rw [chainValue_cons_cons]
    have hih := ih y h.tail (hyz.trans hzL)
    have h18 := collapse_le (le_refl 1) hy1 hyz hzL
    linarith

end
