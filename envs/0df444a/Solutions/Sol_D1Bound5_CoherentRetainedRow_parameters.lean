-- Prove2me | solution 1 for D1Bound5.CoherentRetainedRow.parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:23:08.15811+00:00
-- url     : https://prove2.me/submissions/3537697e-e329-4276-9969-3a5670dc1802

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
import Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
import Theorems.Thm_D1Bound5_coherent_three_parameter_rows

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



theorem _root_.solution {H lam U : ℝ}
    (hrow : CoherentRetainedRow H lam U) :
    1 < H ∧ H ≤ 48 ∧ U ≤ 179/10 ∧
      0 < coherentThreeLowerConstant H ∧ 0 < coherentThreeUpperConstant H ∧
      100*coherentThreeUpperConstant H/99 < lam ∧
      5 < 100/(201*coherentThreeUpperConstant H) ∧
      100/(199*coherentThreeLowerConstant H) < U := by
  rcases hrow with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have h := coherent_three_parameter_rows.1
    exact ⟨by norm_num,by norm_num,le_rfl,h.1,
      by norm_num [coherentThreeUpperConstant,coherentThreeTailConstant],
      h.2.1,h.2.2.1,h.2.2.2⟩
  · have h := coherent_three_parameter_rows.2
    exact ⟨by norm_num,le_rfl,by norm_num,h.1,
      by norm_num [coherentThreeUpperConstant,coherentThreeTailConstant],
      h.2.1,h.2.2.1,h.2.2.2⟩



end D1Bound5
end
