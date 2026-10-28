-- Prove2me | solution 1 for D1Bound5.full_ring_unit_pair_cubic_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:15.315081+00:00
-- url     : https://prove2.me/submissions/ef16609f-2dca-49a8-aab5-7d0850334e72

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_discrete_unit_pair_cubic_growth
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5









/-- Actual common extensions of {-1,1} satisfy the manuscript cubic gap.
All five square witnesses are in the full integer ring; no analytic
branch, root nonvanishing, or auxiliary form estimate is a premise. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (c d : 𝓞 K) (hC : 9 ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖) (hneq : d ≠ -c)
    (hcp : ∃ r : 𝓞 K, r^2 = c+1) (hcm : ∃ r : 𝓞 K, r^2 = 1-c)
    (hdp : ∃ r : 𝓞 K, r^2 = d+1) (hdm : ∃ r : 𝓞 K, r^2 = 1-d)
    (hcd : ∃ r : 𝓞 K, r^2 = c*d+1) :
    ‖phi (c : K)‖^3/2 < ‖phi (d : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hdiscrete (x : 𝓞 K) (hx : x ≠ 0) : 1 ≤ ‖f x‖ :=
    one_le_norm_integer hK phi hx
  have hsum : c+d ≠ 0 := by
    intro h
    apply hneq
    linear_combination h
  have hneqC : f c+f d ≠ 0 := by
    intro h
    have hn := hdiscrete (c+d) hsum
    rw [map_add,h,norm_zero] at hn
    norm_num at hn
  obtain ⟨cp,hcp⟩ := hcp
  obtain ⟨cm,hcm⟩ := hcm
  obtain ⟨dp,hdp⟩ := hdp
  obtain ⟨dm,hdm⟩ := hdm
  obtain ⟨z,hz⟩ := hcd
  apply discrete_unit_pair_cubic_growth f hdiscrete c d z (cp*dp) (cm*dm)
    hC hCD hneqC hz
  · rw [mul_pow,hcp,hdp]
  · rw [mul_pow,hcm,hdm]



end D1Bound5
end
