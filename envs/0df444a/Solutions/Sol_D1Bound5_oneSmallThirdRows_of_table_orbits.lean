-- Prove2me | solution 1 for D1Bound5.oneSmallThirdRows_of_table_orbits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:11.409994+00:00
-- url     : https://prove2.me/submissions/e20fcf67-5ca6-46b8-a2c4-b93d29bf5c9a

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
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_firstPairOrbit_normalize
import Theorems.Thm_D1Bound5_oneSmallSymmetry_square
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_involutive
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm

section
namespace D1Bound5
open QuadInt













/-- The fixed pair representatives classify third entries after one common
normalization, preserving all equal-modulus cases and all square conditions. -/
theorem _root_.solution {tau nu : ℤ}
    (table : List ((ℤ × ℤ) × (ℤ × ℤ)))
    (reps : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (horbits : table.toFinset = reps.biUnion (firstPairOrbit tau))
    (hreps : ∀ row ∈ reps,
      OneSmallThirdRowProperty (firstPairRowA tau nu row) (firstPairRowB tau nu row))
    (a b s : QuadInt tau nu) (hrow : firstPairCoordinates a b ∈ table)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by
  have hmem : firstPairCoordinates a b ∈ reps.biUnion (firstPairOrbit tau) := by
    rw [← horbits]
    exact List.mem_toFinset.mpr hrow
  obtain ⟨rep,hrep,horbit⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨sgn,conj,heA,heB⟩ := firstPairOrbit_normalize a b rep horbit
  let F := smallExtensionSymmetry (tau := tau) (nu := nu) sgn conj
  have hF : Function.Involutive F := smallExtensionSymmetry_involutive sgn conj
  have hnorm (z : QuadInt tau nu) : (F z).norm = z.norm := smallExtensionSymmetry_norm sgn conj z
  have hsbound : (F s).norm ≤ 224 := by simpa only [hnorm] using hbound
  have hsorder : (firstPairRowB tau nu rep).norm ≤ (F s).norm := by
    rw [← heB]
    simpa only [F,smallExtensionSymmetry_norm] using horder
  have hsA : F s ≠ firstPairRowA tau nu rep := by
    rw [← heA]
    exact fun h => ha (hF.injective h)
  have hsB : F s ≠ firstPairRowB tau nu rep := by
    rw [← heB]
    exact fun h => hb (hF.injective h)
  have hsPair : PairExtension (firstPairRowA tau nu rep) (firstPairRowB tau nu rep) (F s) := by
    constructor
    · simpa only [heA] using oneSmallSymmetry_square sgn conj a s hpair.1
    · simpa only [heB] using oneSmallSymmetry_square sgn conj b s hpair.2
  have h := hreps rep hrep (F s) hsbound hsorder hsA hsB hsPair
  refine ⟨sgn,conj,?_⟩
  simpa only [heA,heB] using h

end D1Bound5
end
