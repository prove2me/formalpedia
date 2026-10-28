-- Prove2me | solution 1 for D1Bound5.firstPairTable_geometry_normalize
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:21.668985+00:00
-- url     : https://prove2.me/submissions/892272fd-6d41-48ae-8bc5-bb4a686f3552

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_0_1
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_0_2
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_0_5
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_0_6
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_1
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_2
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_3
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_4
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_5
import Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_6
import Theorems.Thm_D1Bound5_firstPairOrbit_normalize
import Theorems.Thm_D1Bound5_firstPairTable_0_1_orbits
import Theorems.Thm_D1Bound5_firstPairTable_0_2_orbits
import Theorems.Thm_D1Bound5_firstPairTable_0_5_orbits
import Theorems.Thm_D1Bound5_firstPairTable_0_6_orbits
import Theorems.Thm_D1Bound5_firstPairTable_1_1_orbits
import Theorems.Thm_D1Bound5_firstPairTable_1_2_orbits
import Theorems.Thm_D1Bound5_firstPairTable_1_3_orbits
import Theorems.Thm_D1Bound5_firstPairTable_1_4_orbits
import Theorems.Thm_D1Bound5_firstPairTable_1_5_orbits
import Theorems.Thm_D1Bound5_firstPairTable_1_6_orbits

section
namespace D1Bound5
open QuadInt

private theorem firstPairGeometry_normalize_of_orbits {tau nu : ℤ}
    (table : List ((ℤ × ℤ) × (ℤ × ℤ)))
    (reps : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (horbits : table.toFinset = reps.biUnion (firstPairOrbit tau))
    (hcover : reps ⊆ (firstPairGeometryRowsAt tau nu).toFinset)
    (a b : QuadInt tau nu) (hrow : firstPairCoordinates a b ∈ table) :
    ∃ g ∈ firstPairGeometryRows, g.tau=tau ∧ g.nu=nu ∧
      ∃ sgn conj : Bool,
        firstPairCoordinates (smallExtensionSymmetry sgn conj a)
          (smallExtensionSymmetry sgn conj b) = (g.a,g.b) := by
  have hmem : firstPairCoordinates a b ∈ reps.biUnion (firstPairOrbit tau) := by
    rw [←horbits]
    exact List.mem_toFinset.mpr hrow
  obtain ⟨rep,hrep,horbit⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨sgn,conj,heA,heB⟩ := firstPairOrbit_normalize a b rep horbit
  have hc : rep ∈ firstPairGeometryRowsAt tau nu := List.mem_toFinset.mp (hcover hrep)
  unfold firstPairGeometryRowsAt at hc
  obtain ⟨g,hg,hge⟩ := List.mem_map.mp hc
  obtain ⟨hg,hgm⟩ := List.mem_filter.mp hg
  have hgm' : g.tau=tau ∧ g.nu=nu := by simpa using hgm
  refine ⟨g,hg,hgm'.1,hgm'.2,sgn,conj,?_⟩
  rw [heA,heB]
  simpa only [firstPairCoordinates,firstPairRowA,firstPairRowB] using hge.symm

/-- Every classified nonrational first pair has one simultaneous sign
and conjugation normalization to a certified geometry row. -/
theorem _root_.solution {tau nu : ℤ}
    (hmodel : (tau,nu) ∈ smallPairModels) (a b : QuadInt tau nu)
    (hrow : firstPairCoordinates a b ∈ firstPairTable tau nu) :
    ∃ g ∈ firstPairGeometryRows, g.tau=tau ∧ g.nu=nu ∧
      ∃ sgn conj : Bool,
        firstPairCoordinates (smallExtensionSymmetry sgn conj a)
          (smallExtensionSymmetry sgn conj b) = (g.a,g.b) := by
  simp only [smallPairModels,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hmodel
  rcases hmodel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact firstPairGeometry_normalize_of_orbits firstPairs_0_1
      firstPairRepresentatives_0_1 firstPairTable_0_1_orbits
      firstPairGeometryRowsAt_covers_0_1 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_0_2
      firstPairRepresentatives_0_2 firstPairTable_0_2_orbits
      firstPairGeometryRowsAt_covers_0_2 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_0_5
      firstPairRepresentatives_0_5 firstPairTable_0_5_orbits
      firstPairGeometryRowsAt_covers_0_5 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_0_6
      firstPairRepresentatives_0_6 firstPairTable_0_6_orbits
      firstPairGeometryRowsAt_covers_0_6 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_1_1
      firstPairRepresentatives_1_1 firstPairTable_1_1_orbits
      firstPairGeometryRowsAt_covers_1_1 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_1_2
      firstPairRepresentatives_1_2 firstPairTable_1_2_orbits
      firstPairGeometryRowsAt_covers_1_2 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_1_3
      firstPairRepresentatives_1_3 firstPairTable_1_3_orbits
      firstPairGeometryRowsAt_covers_1_3 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_1_4
      firstPairRepresentatives_1_4 firstPairTable_1_4_orbits
      firstPairGeometryRowsAt_covers_1_4 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_1_5
      firstPairRepresentatives_1_5 firstPairTable_1_5_orbits
      firstPairGeometryRowsAt_covers_1_5 a b (by simpa [firstPairTable] using hrow)
  · exact firstPairGeometry_normalize_of_orbits firstPairs_1_6
      firstPairRepresentatives_1_6 firstPairTable_1_6_orbits
      firstPairGeometryRowsAt_covers_1_6 a b (by simpa [firstPairTable] using hrow)
  · simp [firstPairTable,firstPairs_1_8] at hrow

end D1Bound5
end
