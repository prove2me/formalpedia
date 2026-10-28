-- Prove2me | solution 1 for D1Bound5.FrontierTableRow.parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:26:13.92596+00:00
-- url     : https://prove2.me/submissions/c21859bd-42f9-4b66-80a9-29cdcfe5a7a9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
import Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions

section
namespace D1Bound5



/-- All listed parameter rows satisfy the positivity and ordering
conditions needed by the determinant estimate. -/
theorem _root_.solution {alpha beta target : ℝ}
    (h : FrontierTableRow alpha beta target) :
    0 < alpha ∧ 3 ≤ beta ∧ alpha ≤ beta ∧ 5 < alpha*beta ∧
      0 ≤ frontierK alpha beta ∧ 0 ≤ frontierL alpha beta ∧
      0 ≤ frontierQ alpha beta := by
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;>
    norm_num [frontierK, frontierL, frontierQ]



end D1Bound5
end
