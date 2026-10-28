-- Prove2me | solution 1 for D1Bound5.clearedPoleSum_degree_lt_total
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:11.60211+00:00
-- url     : https://prove2.me/submissions/82c51ada-2c7e-44ea-8568-22e31242a0ef

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_clearedPoleNumerator_degree_lt_total
import Theorems.Thm_D1Bound5_clearedPoleNumerator_monic

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











/-- A linear combination of proper-pole numerators is still a proper numerator. -/
theorem _root_.solution (a : ι → R) (e : ι → ℕ)
    (c : (i : ι) → Fin (e i + 1) → R) :
    (∑ i, ∑ j : Fin (e i + 1), C (c i j) * clearedPoleNumerator a e i j).degree <
      (∑ l, (e l + 1) : ℕ) := by
  apply (Polynomial.degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro i hi
  apply (Polynomial.degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro j hj
  have hmul : (C (c i j) * clearedPoleNumerator a e i j).degree ≤
      (clearedPoleNumerator a e i j).degree := by
    have hn := Polynomial.degree_le_of_natDegree_le
      (Polynomial.natDegree_C_mul_le (c i j) (clearedPoleNumerator a e i j))
    rwa [← Polynomial.degree_eq_natDegree
      (clearedPoleNumerator_monic a e i j).ne_zero] at hn
  exact hmul.trans_lt (clearedPoleNumerator_degree_lt_total a e i j)

end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]





end Field

end D1Bound5
end
