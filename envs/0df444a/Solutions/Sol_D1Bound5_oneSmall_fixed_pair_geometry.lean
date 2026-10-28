-- Prove2me | solution 1 for D1Bound5.oneSmall_fixed_pair_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:32.927158+00:00
-- url     : https://prove2.me/submissions/38e7343b-d9cb-4b16-a780-f4b005575996

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_valid
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_sub

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Exact squared moduli and strict distance separation for a normalized
fixed pair in the one-small table. This uses the actual signed or
conjugated elements, so the difference norm keeps its phase information. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (phi : K →+* ℂ) (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (e : QuadInt r.triple.tau r.triple.nu ≃+* 𝓞 K)
    (sgn conj : Bool) (x y : 𝓞 K)
    (hx : smallExtensionSymmetry sgn conj (e.symm x) = r.triple.anchorA)
    (hy : smallExtensionSymmetry sgn conj (e.symm y) = r.triple.anchorB) :
    ‖phi (x : K)‖^2 = (r.a0 : ℝ) ∧
    ‖phi (y : K)‖^2 = (r.b0 : ℝ) ∧
    ‖phi (x : K)-phi (y : K)‖^2 = (r.dab : ℝ) ∧
    ‖phi (x : K)‖ < ‖phi (x : K)-phi (y : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f x‖
  let B := ‖f y‖
  let delta := ‖f x-f y‖
  have hnorm (w : 𝓞 K) : ‖f w‖^2 =
      ((smallExtensionSymmetry sgn conj (e.symm w)).norm : ℝ) := by
    change ‖phi (w : K)‖^2 =
      ((smallExtensionSymmetry sgn conj (e.symm w)).norm : ℝ)
    simpa only [smallExtensionSymmetry_norm,RingEquiv.apply_symm_apply] using
      norm_sq_full_ring_equiv e phi (e.symm w)
  have hAsq : A^2 = (r.a0 : ℝ) := by
    have hh := hnorm x
    rw [hx] at hh
    simpa [OneSmallCutoffRow.a0] using hh
  have hBsq : B^2 = (r.b0 : ℝ) := by
    have hh := hnorm y
    rw [hy] at hh
    simpa [OneSmallCutoffRow.b0] using hh
  have hdsq : delta^2 = (r.dab : ℝ) := by
    have hh := hnorm (x-y)
    simp only [map_sub,smallExtensionSymmetry_sub,hx,hy] at hh
    simpa [delta,OneSmallCutoffRow.dab] using hh
  obtain ⟨_,hAN,hBN,_⟩ := oneSmallCutoffRows_valid r hr
  have hA2 : A^2 ≤ 2 := by
    rw [hAsq]
    rcases hAN with h | ⟨h,_⟩ <;> exact_mod_cast (show r.a0 ≤ 2 by linarith only [h])
  have hB9 : 9 ≤ B^2 := by rw [hBsq]; exact_mod_cast hBN
  have hAB2 : 2*A < B := by
    have ha : 0 ≤ A := norm_nonneg _
    have hb : 0 ≤ B := norm_nonneg _
    nlinarith only [hA2,hB9,ha,hb]
  have htriangle : B ≤ delta+A := by
    have hh := norm_add_le (f y-f x) (f x)
    rw [sub_add_cancel,norm_sub_rev] at hh
    exact hh
  exact ⟨hAsq,hBsq,hdsq,by
    change A < delta
    linarith only [hAB2,htriangle]⟩

end D1Bound5
end
