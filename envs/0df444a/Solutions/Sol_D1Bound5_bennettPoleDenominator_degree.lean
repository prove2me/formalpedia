-- Prove2me | solution 1 for D1Bound5.bennettPoleDenominator_degree
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:34.002979+00:00
-- url     : https://prove2.me/submissions/420182ef-1308-4fa8-ac4a-2825717569a5

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Theorems.Thm_D1Bound5_bennettPoleDenominator_monic
import Theorems.Thm_D1Bound5_bennettPoleDenominator_natDegree

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







theorem _root_.solution (a : ι → R) (e : ι → ℕ) :
    (bennettPoleDenominator a e).degree = (∑ i, (e i + 1) : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (bennettPoleDenominator_monic a e).ne_zero,
    bennettPoleDenominator_natDegree]





end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]





end Field

end D1Bound5
end
