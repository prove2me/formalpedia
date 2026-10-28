-- Prove2me | solution 1 for D1Bound5.full_ring_unit_pair_arithmetic_model
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:36.216992+00:00
-- url     : https://prove2.me/submissions/958793a8-fb59-4ced-8107-e814bc5b75c9

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_squarefree_trace_one_discriminant
import Theorems.Thm_D1Bound5_squarefree_trace_zero_parameter

section
open scoped NumberField QuadraticAlgebra
open Module

namespace D1Bound5









/-- Existence of the combined model for the full integer ring, including
the half-integral basis. All arithmetic properties are proved here. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) : Nonempty (UnitPairArithmeticModel (𝓞 K)) := by
  obtain ⟨tau,nu,htau,hd,⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  rcases htau with rfl | rfl
  · have hnu : 0 < nu := by
      unfold QuadInt.discriminant at hd
      norm_num at hd
      omega
    exact ⟨(unitPairTraceZeroModel nu hnu
      (squarefree_trace_zero_parameter e hd)).mapEquiv e⟩
  · have hsq : Squarefree (4*nu-1) := by
      simpa [QuadInt.discriminant] using squarefree_trace_one_discriminant e hd
    exact ⟨(unitPairTraceOneModel nu hd hsq).mapEquiv e⟩





end D1Bound5
end
