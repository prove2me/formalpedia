-- Prove2me | solution 1 for D1Bound5.clearedPoleNumerator_degree_lt_total
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:17.920739+00:00
-- url     : https://prove2.me/submissions/ce974195-08a9-4374-a451-d9b60bd96b79

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_clearedPoleNumerator_monic
import Theorems.Thm_D1Bound5_clearedPoleNumerator_natDegree

section
open Finset Polynomial

namespace D1Bound5

/-!
This module proves existence of the exact cleared partial-fraction decomposition
used by the residue-sum argument. The decomposition is a conclusion, not an
assumption. Identifying its coefficients with the manuscript's explicit finite
binomial sums remains a separate obligation.
-/

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]









/-- Every cleared proper-pole numerator has smaller degree than the denominator. -/
theorem _root_.solution (a : ι → R) (e : ι → ℕ)
    (i : ι) (j : Fin (e i + 1)) :
    (clearedPoleNumerator a e i j).degree < (∑ l, (e l + 1) : ℕ) := by
  apply (Polynomial.natDegree_lt_iff_degree_lt
    (clearedPoleNumerator_monic a e i j).ne_zero).mp
  rw [clearedPoleNumerator_natDegree]
  have hsum := Finset.add_sum_erase (Finset.univ : Finset ι)
    (fun l : ι ↦ e l + 1) (Finset.mem_univ i)
  have hj := j.isLt
  omega



end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]





end Field

end D1Bound5
end
