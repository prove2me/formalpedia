-- Prove2me | solution 1 for D1Bound5.exists_root_error_rational_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:57.181999+00:00
-- url     : https://prove2.me/submissions/e3c0c22a-5a16-40a3-a309-c6204a499b1f

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_root_error_control

section
namespace D1Bound5

/-- A rational first-order margin yields any certified near-half
envelope. This permits a separate sharp constant for each of six edges. -/
theorem _root_.solution (x t : ℂ) (m c k : ℝ)
    (hm : 0 < m) (hc : 0 ≤ c) (hk : 1/2 < k)
    (hgap : 1 < (1-c^2)*m)
    (hprecision : 1 ≤ 2*m*(1+c)^2*(k-1/2))
    (hx : m ≤ ‖x‖) (ht : t^2 = x*(x+1)) :
    ∃ v : ℂ, (v = t ∨ v = -t) ∧ ‖v-x-(1/2 : ℂ)‖ ≤ k-1/2 := by
  have hcoef : 0 ≤ 1-c^2 := by
    by_contra hbad
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hbad)) hm.le
    nlinarith only [hgap,hh]
  have hgap' : 1 < (1-c^2)*‖x‖ :=
    hgap.trans_le (mul_le_mul_of_nonneg_left hx hcoef)
  obtain ⟨v,hv,_,hhalf⟩ := exists_root_error_control x t c hc (hm.trans_le hx) hgap' ht
  refine ⟨v,hv,?_⟩
  have hE : 0 ≤ ‖v-x-(1/2 : ℂ)‖ := norm_nonneg _
  have hscale := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (1+c))) hE
  by_contra hbad
  have hdiff := mul_nonneg
    (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hbad)))
    (show 0 ≤ 2*m*(1+c)^2 by positivity)
  nlinarith only [hhalf,hprecision,hscale,hdiff]









end D1Bound5
end
