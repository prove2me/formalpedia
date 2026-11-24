-- Prove2me | solution 1 for Formalism.G0.QVandermondeP.form1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:56.767315+00:00
-- url     : https://prove2.me/submissions/1830f295-9e75-4633-808a-b008d557c3e1

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Theorems.Thm_Formalism_G0_QVandermondeP_form2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.QVandermondeP
namespace Formalism.G0.QVandermondeP
theorem _root_.solution (q m g n : ℕ) : gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ (l * (m + l - n)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  rw [Nat.add_comm m g, form2 q g m n]
  refine (Finset.sum_range_reflect _ _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ n := by
    have := Finset.mem_range.mp hl
    omega
  have e1 : n + 1 - 1 - l = n - l := by omega
  have e2 : n - (n - l) = l := by omega
  have e3 : m - (n - l) = m + l - n := by omega
  simp only [e1, e2, e3]
  ring
end Formalism.G0.QVandermondeP
