-- Prove2me | solution 1 for D1Bound5.full_small_pair_model_allowed
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:52:29.817498+00:00
-- url     : https://prove2.me/submissions/eec0238b-d1ca-4ce3-bf59-581da4bc1a8a

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_squarefree_trace_one_discriminant
import Theorems.Thm_D1Bound5_squarefree_trace_zero_parameter
import Theorems.Thm_D1Bound5_trace_zero_parameter_not_three_mod_four

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



/-- Maximality excludes the five extraneous coordinate orders in the finite
rectangle. It is used only here, after complete finite-order classification. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (htau : tau = 0 ∨ tau = 1) (hd : 0 < discriminant tau nu)
    (hlo : 1 ≤ nu) (hhi : nu ≤ 8) : (tau,nu) ∈ smallPairModels := by
  rcases htau with rfl | rfl
  · interval_cases nu
    · decide
    · decide
    · have h := trace_zero_parameter_not_three_mod_four e
      norm_num at h
    · have h := squarefree_trace_zero_parameter e hd
      have hu : IsUnit (2 : ℤ) := h 2 (by decide)
      norm_num [Int.isUnit_iff] at hu
    · decide
    · decide
    · have h := trace_zero_parameter_not_three_mod_four e
      norm_num at h
    · have h := squarefree_trace_zero_parameter e hd
      have hu : IsUnit (2 : ℤ) := h 2 (by decide)
      norm_num [Int.isUnit_iff] at hu
  · interval_cases nu
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · have h := squarefree_trace_one_discriminant e hd
      have h27 : Squarefree (27 : ℤ) := by simpa [discriminant] using h
      have hu : IsUnit (3 : ℤ) := h27 3 (by decide)
      norm_num [Int.isUnit_iff] at hu
    · decide



end D1Bound5
end
