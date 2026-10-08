-- Prove2me | solution 1 for ErschlerZheng.satisfiesFr_five_firstString
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T02:32:46.804978+00:00
-- url     : https://prove2.me/submissions/4529f48a-18f5-4dba-81a8-0306cc50ce64

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# A16 and A18: `(012)^∞` satisfies `Fr(5)`; `L^ω_{n+1} ⩾ 2 L^ω_n`

A18 route (the paper's idea): the row vector `r_n = (1 1 1) M_{ω_0} ⋯ M_{ω_{n-1}}` keeps each
coordinate at most the sum of the other two, and `Σ (r M_i) ⩾ 2 Σ r` for such `r`.
-/

namespace ErschlerZheng

namespace LengthsDev

end LengthsDev

end ErschlerZheng
end

section
open ErschlerZheng
theorem solution : SatisfiesFr 5 firstString := by
  intro k
  refine ⟨(5 - (k * 5) % 3) % 3, by omega, ?_, ?_, Or.inl ?_⟩ <;>
    apply Fin.ext <;> simp [firstString] <;> omega
end
