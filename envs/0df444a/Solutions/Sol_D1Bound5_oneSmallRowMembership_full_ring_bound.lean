-- Prove2me | solution 1 for D1Bound5.oneSmallRowMembership_full_ring_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:53:27.268149+00:00
-- url     : https://prove2.me/submissions/84d1937d-bbf4-4413-b6c0-3862e3706d29

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_oneSmallFixedRows_bounded_growth
import Theorems.Thm_D1Bound5_oneSmallSymmetry_square
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt



/-- Every bounded fourth-entry certificate transports to arbitrary actual
full-ring entries through the same sign/conjugation normalization used in
the complete first-triple classification. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K) (phi : K →+* ℂ)
    (sgn conj : Bool) (a b s z : 𝓞 K) (cutoff : ℤ)
    (hrow : OneSmallRowMembership
      (smallExtensionSymmetry sgn conj (e.symm a))
      (smallExtensionSymmetry sgn conj (e.symm b))
      (smallExtensionSymmetry sgn conj (e.symm s)) cutoff)
    (hz : ‖phi (z : K)‖^2 < (cutoff : ℝ))
    (ha : ∃ q : 𝓞 K, q*q = a*z+1) (hb : ∃ q : 𝓞 K, q*q = b*z+1)
    (hs : ∃ q : 𝓞 K, q*q = s*z+1) :
    ‖phi (z : K)‖^2 ≤ 4*‖phi (b : K)‖^2*‖phi (s : K)‖^2 := by
  classical
  let F : 𝓞 K → QuadInt tau nu := fun w => smallExtensionSymmetry sgn conj (e.symm w)
  have hnorm (w : 𝓞 K) : ‖phi (w : K)‖^2 = ((F w).norm : ℝ) := by
    simpa only [F,smallExtensionSymmetry_norm,RingEquiv.apply_symm_apply] using
      norm_sq_full_ring_equiv e phi (e.symm w)
  have hroots (w : 𝓞 K) (h : ∃ q : 𝓞 K, q*q = w*z+1) :
      ∃ q : QuadInt tau nu, q*q = F w*F z+1 := by
    obtain ⟨q,hq⟩ := h
    apply oneSmallSymmetry_square sgn conj
    exact ⟨e.symm q,by simpa only [map_mul,map_add,map_one] using congrArg e.symm hq⟩
  have hz' : (F z).norm < cutoff := by
    rw [hnorm z] at hz
    exact_mod_cast hz
  let r : OneSmallTripleRow :=
    ⟨tau,nu,((F a).re,(F a).im),((F b).re,(F b).im),((F s).re,(F s).im),cutoff⟩
  have hr : r ∈ oneSmallFixedRows := hrow
  have hg := oneSmallFixedRows_bounded_growth r hr (F z) hz'
    (hroots a ha) (hroots b hb) (hroots s hs)
  have hreal : ((F z).norm : ℝ) ≤ 4*((F b).norm : ℝ)*((F s).norm : ℝ) := by
    exact_mod_cast hg
  rwa [← hnorm z,← hnorm b,← hnorm s] at hreal



end D1Bound5
end
