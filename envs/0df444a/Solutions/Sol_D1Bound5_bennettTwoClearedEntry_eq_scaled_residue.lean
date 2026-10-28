-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_eq_scaled_residue
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:08.490699+00:00
-- url     : https://prove2.me/submissions/34362fcd-6d4d-49a6-8dad-d26112c9c28b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_homogenize

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

























/-- Exact identification with the manuscript's clearing factor applied to
the original residue coefficient f=P(1/N), with H=ab and N=abc. -/
theorem _root_.solution
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (k : ℕ) (i j : Fin 3) :
    bennettTwoClearedEntry a b c k i j =
      (4 * (a * b) ^ 2 * c * (a - b) ^ 2) ^ k *
        (bennettPolynomialResidue Finset.univ (bennettTwoNodes a b) k (1 / 2 : F)
          i j).eval ((a * b * c)⁻¹) := by
  have hN : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hs : 4 * (a * b) ^ 2 * c * (a - b) ^ 2 =
      (4 * a * b * (a - b) ^ 2) * (a * b * c) := by ring
  rw [hs, mul_pow, mul_assoc, bennettPolynomialResidue_homogenize
    Finset.univ (bennettTwoNodes a b) k (1 / 2 : F) (a * b * c) i j hN] <;> rfl



end D1Bound5
end
