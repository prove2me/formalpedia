-- Prove2me | solution 1 for D1Bound5.UnitPairArithmeticModel.pellIntegerSquare
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:45.731571+00:00
-- url     : https://prove2.me/submissions/b481b5c6-3c28-4938-84aa-442a9ab8f486

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
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Theorems.Thm_D1Bound5_full_ring_positive_integer_square

section
open scoped NumberField
open Module

namespace D1Bound5





/-- Convert actual full-ring squares of ordinary integers using the same
fixed d as the Pell description, including zero and negative radicands. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (M : UnitPairArithmeticModel (𝓞 K))
    (m : ℤ) (hs : ∃ r : 𝓞 K, r*r = (m : 𝓞 K)) : PellIntegerSquare M.d m := by
  by_cases hm : 0 < m
  · obtain ⟨r,hr⟩ := full_ring_positive_integer_square hK hm hs
    exact Or.inl ⟨r,by nlinarith [hr]⟩
  · obtain ⟨r,hr⟩ := M.negative_square m (by omega) hs
    exact Or.inr ⟨r,by nlinarith [hr]⟩





end D1Bound5
end
