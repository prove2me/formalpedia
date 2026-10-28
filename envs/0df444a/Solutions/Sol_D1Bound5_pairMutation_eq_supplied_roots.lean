-- Prove2me | solution 1 for D1Bound5.pairMutation_eq_supplied_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:14.257895+00:00
-- url     : https://prove2.me/submissions/3ed4affd-acbf-4fe0-85b1-9aa4c3f8d0d8

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_rootCandidate_complete
import Theorems.Thm_D1Bound5_mutate_eq_supplied_roots

section
namespace D1Bound5
open QuadInt













/-- Both original deterministic neighbors are among the supplied-root
mutations. Canonical roots occur only in this symbolic soundness proof. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b z r0 r s : QuadInt tau nu)
    (h0 : r0 * r0 = a * b + 1) (hr : r * r = a * z + 1)
    (hs : s * s = b * z + 1) {w : QuadInt tau nu}
    (hw : w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z) :
    w = mutate a b z r0 r s ∨ w = mutate a b z r0 r (-s) := by
  have hc0 := rootCandidate_complete hd (show ∃ q, q * q = a * b + 1 from ⟨r0, h0⟩)
  have hcr := rootCandidate_complete hd (show ∃ q, q * q = a * z + 1 from ⟨r, hr⟩)
  have hcs := rootCandidate_complete hd (show ∃ q, q * q = b * z + 1 from ⟨s, hs⟩)
  rcases hw with rfl | rfl
  · exact mutate_eq_supplied_roots hd a b z r0 r s _ _ _ h0 hr hs hc0 hcr hcs
  · exact mutate_eq_supplied_roots hd a b z r0 r s _ _ _ h0 hr hs hc0 hcr
      (by simpa only [neg_mul_neg] using hcs)







end D1Bound5
end
