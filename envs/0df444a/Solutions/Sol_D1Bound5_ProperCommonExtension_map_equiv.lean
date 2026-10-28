-- Prove2me | solution 1 for D1Bound5.ProperCommonExtension.map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:21.241674+00:00
-- url     : https://prove2.me/submissions/43a36ea6-fe6c-4c44-9be7-49b438edf340

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt







/-- Proper common extensions transport through an actual ring equivalence. -/
theorem _root_.solution
    {R S : Type*} [CommRing R] [CommRing S] [DecidableEq R] [DecidableEq S]
    (e : R ≃+* S) (A : Finset R) (z : R) (hz : ProperCommonExtension A z) :
    ProperCommonExtension (A.image e) (e z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hz.1
    apply e.injective
    simpa only [map_zero] using h
  · intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    exact hz.2.1 ((e.injective he) ▸ ha)
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r, hr⟩ := hz.2.2 a' ha'
    exact ⟨e r, by simpa only [map_mul, map_add, map_one] using congrArg e hr⟩



















end D1Bound5
end
