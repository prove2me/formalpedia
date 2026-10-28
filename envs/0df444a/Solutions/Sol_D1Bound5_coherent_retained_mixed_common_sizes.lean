-- Prove2me | solution 1 for D1Bound5.coherent_retained_mixed_common_sizes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:22.450472+00:00
-- url     : https://prove2.me/submissions/0637b714-31fc-41a1-8ba0-a1c3b3367ec9

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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5





/-- The mixed retained power gap with AT≥48 supplies the common large
terminal hypotheses for the approximation constructions. -/
theorem _root_.solution
    (A S T C : ℝ) (hA : 1 ≤ A) (hS3 : 3 ≤ S) (hST : S ≤ T)
    (hAT48 : 48 ≤ A*T) (hgap : A^2*T^5/S^2 < C) :
    1000 < C ∧ 200*S < C ∧ 4*T < C := by
  have hS : 0 < S := by linarith only [hS3]
  have hT : 0 < T := hS.trans_le hST
  have hbase : A^2*T^3 ≤ A^2*T^5/S^2 := by
    apply (le_div_iff₀ (pow_pos hS 2)).2
    have hs : S^2 ≤ T^2 := by gcongr
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ A^2*T^3)
    nlinarith only [hh]
  have hT3 : A^2*T^3 < C := hbase.trans_lt hgap
  have hAT2 : (2304 : ℝ) ≤ A^2*T^2 := by nlinarith only [hAT48,sq_nonneg (A*T-48)]
  have hmul := mul_le_mul_of_nonneg_right hAT2 hT.le
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hS3,hST,hmul,hT3]
  · nlinarith only [hST,hS,hmul,hT3]
  · nlinarith only [hT,hmul,hT3]

end D1Bound5
end
