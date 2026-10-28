-- Prove2me | solution 1 for D1Bound5.coherent_three_parameter_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:29.407879+00:00
-- url     : https://prove2.me/submissions/7df1a4ce-293c-47ee-946a-7566276a24ae

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
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions

section
open Finset

noncomputable section

namespace D1Bound5















/-- All exact rational comparisons for the manuscript's two rows. -/
theorem _root_.solution :
    (0 < coherentThreeLowerConstant 32 ∧
      100*coherentThreeUpperConstant 32/99 < (1/10 : ℝ) ∧
      5 < 100/(201*coherentThreeUpperConstant 32) ∧
      100/(199*coherentThreeLowerConstant 32) < 179/10) ∧
    (0 < coherentThreeLowerConstant 48 ∧
      100*coherentThreeUpperConstant 48/99 < (19/200 : ℝ) ∧
      5 < 100/(201*coherentThreeUpperConstant 48) ∧
      100/(199*coherentThreeLowerConstant 48) < 15) := by
  norm_num [coherentThreeLowerConstant, coherentThreeUpperConstant, coherentThreeTailConstant]

end D1Bound5
end
