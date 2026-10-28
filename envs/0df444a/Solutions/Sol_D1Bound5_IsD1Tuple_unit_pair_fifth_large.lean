-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.unit_pair_fifth_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:29:38.294986+00:00
-- url     : https://prove2.me/submissions/0d6310ed-2579-489a-855e-0c723f5c3396

import Init
import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_unit_pair_finite_field_model
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_full_ring_unit_pair_pell_no_three_bounded

section
open scoped NumberField
open Module

namespace D1Bound5



/-- Actual ordered sextuples containing {-1,1} have their fifth entry beyond
radius 10^550. The field restriction and the real-axis reduction are derived
from the sextuple itself; no field list or Pell-completeness assumption is
left at this endpoint. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hm : t 0 = -1) (hp : t 1 = 1)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖)) :
    (10 : ℝ)^550 < ‖phi (t 4 : K)‖ := by
  by_contra hbig
  have hsmall : ‖phi (t 4 : K)‖ ≤ (10 : ℝ)^550 := le_of_not_gt hbig
  obtain ⟨M,hd,hupper,hmod,hreal⟩ := ht.unit_pair_finite_field_model hK phi t hm hp hmon
  let e : Fin 3 → Fin 6 := fun i => ⟨i.val+2,by omega⟩
  let s : Fin 3 → 𝓞 K := fun i => t (e i)
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp [e] at hv
    omega
  have hs : IsD1Tuple s := by
    refine ⟨ht.1.comp he,fun i => ht.2.1 (e i),?_⟩
    intro i j hij
    exact ht.2.2 (e i) (e j) (fun h => hij (he h))
  apply full_ring_unit_pair_pell_no_three_bounded hK phi M hd hupper hmod s hs
  · intro i
    simpa only [s,e,Fin.val_castSucc] using hreal i.castSucc
  · intro i
    have hi : e i ≤ (4 : Fin 6) := by change i.val+2 ≤ 4; omega
    have hlo : ‖phi (s i : K)‖ ≤ (10 : ℝ)^550 :=
      (hmon hi).trans hsmall
    have hnorm := norm_nonneg (phi (s i : K))
    have hpow : 0 ≤ (10 : ℝ)^550 := by positivity
    have hprod := mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hpow hnorm)
    have heq : ((10 : ℝ)^550)^2 = (10 : ℝ)^1100 := by rw [← pow_mul]
    nlinarith only [hprod,heq]

end D1Bound5
end
