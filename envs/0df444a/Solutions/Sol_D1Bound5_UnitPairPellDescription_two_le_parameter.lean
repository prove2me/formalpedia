-- Prove2me | solution 1 for D1Bound5.UnitPairPellDescription.two_le_parameter
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:55.034443+00:00
-- url     : https://prove2.me/submissions/14d37465-38e4-4451-a860-574faf050abc

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions

section
namespace D1Bound5



private theorem unit_pair_norm_two_d_ne_one (u v : ℤ) : u^2-v^2 ≠ 2 := by
  intro h
  have hm := congrArg (fun a : ℤ => a % 4) h
  have hu0 : 0 ≤ u % 4 := Int.emod_nonneg _ (by decide)
  have hu4 : u % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  have hv0 : 0 ≤ v % 4 := Int.emod_nonneg _ (by decide)
  have hv4 : v % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  interval_cases hu : u % 4 <;> interval_cases hv : v % 4 <;>
    norm_num [Int.sub_emod,pow_two,Int.mul_emod,hu,hv] at hm

private theorem unit_pair_norm_one_d_ne_one (u v : ℤ) (hv : v ≠ 0) : u^2-v^2 ≠ 1 := by
  intro h
  have hp : (u-v)*(u+v) = 1 := by nlinarith only [h]
  have hu : IsUnit (u-v) := isUnit_of_dvd_one ⟨u+v,hp.symm⟩
  have hcases : u-v = 1 ∨ u-v = -1 := Int.isUnit_iff.mp hu
  rcases hcases with hc | hc
  · have hu : u = v+1 := by omega
    rw [hu] at h
    have hzero : v = 0 := by nlinarith only [h]
    exact hv hzero
  · have hu : u = v-1 := by omega
    rw [hu] at h
    have hzero : v = 0 := by nlinarith only [h]
    exact hv hzero

/-- The Gaussian parameter admits no nonzero unit-pair extension in
either Pell branch. This is independent of any growth or finite search. -/
theorem _root_.solution
    {R : Type*} [Ring R] (d : ℤ) (w z : R) (hd : 0 < d)
    (h : UnitPairPellDescription d w z) : 2 ≤ d := by
  by_contra hh
  have hd1 : d = 1 := by omega
  subst d
  rcases h with ⟨u,v,_,hPell,_⟩ | ⟨u,v,hv,hPell,_⟩
  · exact unit_pair_norm_two_d_ne_one u v (by simpa only [one_mul] using hPell)
  · exact unit_pair_norm_one_d_ne_one u v hv (by simpa only [one_mul] using hPell)



open scoped NumberField
open Module



end D1Bound5
end
