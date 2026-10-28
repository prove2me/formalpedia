-- Prove2me | solution 1 for D1Bound5.firstPairTable_third_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:08.306043+00:00
-- url     : https://prove2.me/submissions/5746aecd-4198-45a6-a748-d3838ccda2bc

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
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_firstPairTable_0_1_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_0_2_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_0_5_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_0_6_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_1_1_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_1_2_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_1_3_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_1_4_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_1_5_third_rows
import Theorems.Thm_D1Bound5_firstPairTable_1_6_third_rows

section
namespace D1Bound5
open QuadInt





















theorem _root_.solution {tau nu : ℤ}
    (hmodel : (tau,nu) ∈ smallPairModels) (a b s : QuadInt tau nu)
    (hrow : firstPairCoordinates a b ∈ firstPairTable tau nu)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by
  simp only [smallPairModels, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmodel
  rcases hmodel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact firstPairTable_0_1_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_0_2_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_0_5_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_0_6_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_1_1_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_1_2_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_1_3_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_1_4_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_1_5_third_rows a b s hrow hbound horder ha hb hpair
  · exact firstPairTable_1_6_third_rows a b s hrow hbound horder ha hb hpair
  · simp [firstPairTable,firstPairs_1_8] at hrow

end D1Bound5
end
