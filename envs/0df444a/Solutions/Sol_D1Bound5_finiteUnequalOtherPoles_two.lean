-- Prove2me | solution 1 for D1Bound5.finiteUnequalOtherPoles_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:13.02092+00:00
-- url     : https://prove2.me/submissions/ab542662-270e-4703-9925-cdb38b53006e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions
import Theorems.Thm_D1Bound5_finiteUnequalOrders_add_one

section
open Finset

namespace D1Bound5









variable {F : Type*} [Field F] [CharZero F]





theorem _root_.solution (x y : F) (k m : ℕ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (i : Fin 3) :
    bennettLocalReciprocal (bennettTwoNodes x y) (finiteUnequalOrders k m i) 2 =
      bennettPoleSeries x (m+if i=0 then 1 else 0)*
        bennettPoleSeries (x-y) (k+if i=1 then 1 else 0) := by
  have hh : (Finset.univ : Finset (Fin 3)).erase 2 = {0,1} := by decide
  simp [bennettLocalReciprocal,hh,finiteUnequalOrders_add_one k m hk hm, bennettTwoNodes, Matrix.cons_val_two]









end D1Bound5
end
