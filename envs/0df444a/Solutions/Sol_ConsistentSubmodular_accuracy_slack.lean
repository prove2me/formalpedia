-- Prove2me | solution 1 for ConsistentSubmodular.accuracy_slack
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:45.516203+00:00
-- url     : https://prove2.me/submissions/a8c1f4b3-0d3f-47ff-a6c5-16c52ef8e955

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound

section

noncomputable section

namespace ConsistentSubmodular

theorem accuracy_ge (ε : ℝ) : 200 ≤ accuracy ε := Nat.le_add_left _ _

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution {ε : ℝ} (hε : 0 < ε) : 20 * ((1 : ℝ) / accuracy ε) < ε := by
  have hNpos : (0 : ℝ) < accuracy ε := by
    have := accuracy_ge ε
    exact_mod_cast (show 0 < accuracy ε by omega)
  have hN : 20 / ε < (accuracy ε : ℝ) := by
    unfold accuracy
    push_cast
    have := Nat.lt_floor_add_one (20 / ε)
    linarith
  rw [mul_one_div, div_lt_iff₀ hNpos]
  have := (div_lt_iff₀ hε).mp hN
  linarith

end
