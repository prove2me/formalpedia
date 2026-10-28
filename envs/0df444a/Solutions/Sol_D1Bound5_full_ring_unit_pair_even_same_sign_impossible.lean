-- Prove2me | solution 1 for D1Bound5.full_ring_unit_pair_even_same_sign_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:40.956032+00:00
-- url     : https://prove2.me/submissions/16f3007b-1c3d-442c-a295-027dc874fd2f

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
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_full_ring_positive_integer_square

section
open scoped NumberField
open Module

namespace D1Bound5









/-- Two positive magnitudes three modulo four cannot have their product
plus one a square in any imaginary quadratic full integer ring. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (m n : ℤ)
    (hm : 0 < m) (hn : 0 < n) (hm4 : m % 4 = 3) (hn4 : n % 4 = 3)
    (hs : ∃ r : 𝓞 K, r * r = ((m * n + 1 : ℤ) : 𝓞 K)) : False := by
  have hpos : 0 < m * n + 1 := by nlinarith [mul_pos hm hn]
  obtain ⟨r, hr⟩ := full_ring_positive_integer_square hK hpos hs
  have hmod := congrArg (fun x : ℤ => x % 4) hr
  have hr0 : 0 ≤ r % 4 := Int.emod_nonneg _ (by decide)
  have hr4 : r % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  interval_cases hr' : r % 4 <;>
    norm_num [Int.add_emod, Int.mul_emod, pow_two, hm4, hn4, hr'] at hmod

end D1Bound5
end
