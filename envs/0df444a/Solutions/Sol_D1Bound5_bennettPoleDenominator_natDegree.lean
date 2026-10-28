-- Prove2me | solution 1 for D1Bound5.bennettPoleDenominator_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:32.813636+00:00
-- url     : https://prove2.me/submissions/3c62e34d-da33-43ff-9edc-7ec5c900fede

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions

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
    (bennettPoleDenominator a e).natDegree = ∑ i, (e i + 1) := by
  unfold bennettPoleDenominator
  rw [Polynomial.natDegree_prod_of_monic
    (h := fun i _ ↦ (Polynomial.monic_X_sub_C (a i)).pow (e i + 1))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Polynomial.monic_X_sub_C (a i)).natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]







end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]





end Field

end D1Bound5
end
