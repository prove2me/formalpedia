-- Prove2me | solution 1 for D1Bound5.coherent_analytic_two_ne_zero_of_not_regular
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:45.74405+00:00
-- url     : https://prove2.me/submissions/82a2b3e8-5d19-4e3a-8e7f-8cb1609dc6f8

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Theorems.Thm_D1Bound5_coherent_analytic_anchor_root_sq
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_two_vanishing_regular_equation

section
namespace D1Bound5



/-- The actual analytic coherent form is nonzero whenever the
regular-quadruple equation fails.  All of its square identities are
derived from the branch-fixed analytic construction. -/
theorem _root_.solution
    (a b p q eta : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hab : a ≠ b)
    (heta : eta ^ 2 = p * q)
    (hreg : (a + b - p - q) ^ 2 ≠ 4 * (a * b + 1) * (p * q + 1)) :
    coherentAnchorRoot a p q eta - coherentAnchorRoot b p q eta -
      (a - b) * coherentTerminalRoot p q eta ≠ 0 := by
  intro hzero
  apply hreg
  exact coherent_two_vanishing_regular_equation a b p q
    (coherentAnchorRoot a p q eta) (coherentAnchorRoot b p q eta)
    (coherentTerminalRoot p q eta) hab
    (coherent_analytic_anchor_root_sq a p q eta ha hp hq heta)
    (coherent_analytic_anchor_root_sq b p q eta hb hp hq heta)
    (coherent_analytic_terminal_root_sq p q eta hp hq heta) hzero

end D1Bound5
end
