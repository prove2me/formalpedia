-- Prove2me | solution 1 for D1Bound5.coherent_analytic_two_ne_zero_of_large_terminal
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:26.23303+00:00
-- url     : https://prove2.me/submissions/71a8aedc-88f4-48e8-bcca-293ef21f5ea7

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Theorems.Thm_D1Bound5_coherent_analytic_two_ne_zero_of_not_regular
import Theorems.Thm_D1Bound5_regular_quadruple_norm_lt_five

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5







/-- The manuscript's actual large-terminal size hypothesis forces the
two-anchor coherent form nonzero, with no nonvanishing premise. -/
theorem _root_.solution
    (a b p q eta r s t : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hab : a ≠ b)
    (heta : eta ^ 2 = p * q)
    (hr : r ^ 2 = a * b + 1) (hs : s ^ 2 = a * p + 1)
    (ht : t ^ 2 = b * p + 1)
    (hA : 1 ≤ ‖a‖) (hB : 3 ≤ ‖b‖) (hP : 5 * ‖b‖ ≤ ‖p‖)
    (hQ : 5 * ‖a‖ * ‖b‖ * ‖p‖ ≤ ‖q‖) :
    coherentAnchorRoot a p q eta - coherentAnchorRoot b p q eta -
      (a - b) * coherentTerminalRoot p q eta ≠ 0 := by
  apply coherent_analytic_two_ne_zero_of_not_regular a b p q eta ha hb hp hq hab heta
  intro hreg
  exact (not_lt_of_ge hQ) (regular_quadruple_norm_lt_five a b p q r s t
    hr hs ht hreg hA hB hP)



end D1Bound5
end
