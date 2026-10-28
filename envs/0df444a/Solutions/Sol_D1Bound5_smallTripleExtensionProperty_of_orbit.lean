-- Prove2me | solution 1 for D1Bound5.smallTripleExtensionProperty_of_orbit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:57:46.540988+00:00
-- url     : https://prove2.me/submissions/1e791dcc-54e4-4e8f-b09a-9bd7aa255148

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
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_SmallTripleExtensionProperty_symmetry

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

























/-- The explicit coordinate orbit in the finite classification is exactly
covered by the four proved norm-preserving extension symmetries. -/
theorem _root_.solution {tau nu : ℤ}
    (row row' : Finset (ℤ × ℤ))
    (hrow : SmallTripleExtensionProperty (smallCoordinateSet tau nu row))
    (horbit : row' ∈ smallTripleOrbit tau row) :
    SmallTripleExtensionProperty (smallCoordinateSet tau nu row') := by
  have himage (sgn conj : Bool) (g : ℤ × ℤ → ℤ × ℤ)
      (hg : ∀ p, (⟨(g p).1, (g p).2⟩ : QuadInt tau nu) =
        smallExtensionSymmetry sgn conj ⟨p.1,p.2⟩) :
      smallCoordinateSet tau nu (row.image g) =
        (smallCoordinateSet tau nu row).image (smallExtensionSymmetry sgn conj) := by
    unfold smallCoordinateSet
    rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro p _
    exact hg p
  simp only [smallTripleOrbit, Finset.mem_insert, Finset.mem_singleton] at horbit
  rcases horbit with rfl | rfl | rfl | rfl
  · exact hrow
  · rw [himage true false (fun p => (-p.1,-p.2)) (by
      intro p; apply QuadraticAlgebra.ext <;> simp [smallExtensionSymmetry])]
    exact SmallTripleExtensionProperty.symmetry _ hrow true false
  · rw [himage false true (fun p => (p.1+tau*p.2,-p.2)) (by
      intro p; apply QuadraticAlgebra.ext <;> simp [smallExtensionSymmetry])]
    exact SmallTripleExtensionProperty.symmetry _ hrow false true
  · rw [himage true true (fun p => (-p.1-tau*p.2,p.2)) (by
      intro p; apply QuadraticAlgebra.ext <;> simp [smallExtensionSymmetry] <;> ring)]
    exact SmallTripleExtensionProperty.symmetry _ hrow true true

end D1Bound5
end
