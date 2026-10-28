-- Prove2me | solution 1 for D1Bound5.eisenstein_degenerate_pair
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:55:55.964967+00:00
-- url     : https://prove2.me/submissions/21a9da4e-fc41-4b7a-b4c2-e1fd555c9cfe

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
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
import Definitions.Def_D1Bound5_DegeneratePairClassification_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff
import Theorems.Thm_D1Bound5_product_neg_one_norms

section
namespace D1Bound5
open QuadInt













private theorem eisenstein_degenerate_checked :
    ∀ a ∈ disk 1 1 1, ∀ b ∈ disk 1 1 1,
      a ≠ b → a*b+1=0 → RationalUnitPair a b ∨
        EisensteinCanonicalPair a b ∨ EisensteinCanonicalPair (-a) (-b) := by
  unfold RationalUnitPair EisensteinCanonicalPair
  decide +kernel

theorem _root_.solution (a b : QuadInt 1 1) (hne : a ≠ b)
    (hprod : a*b+1=0) : RationalUnitPair a b ∨
      EisensteinCanonicalPair a b ∨ EisensteinCanonicalPair (-a) (-b) := by
  obtain ⟨ha,hb⟩ := product_neg_one_norms (by decide) a b hprod
  exact eisenstein_degenerate_checked a ((mem_disk_iff (by decide) 1 a).2 ha.le)
    b ((mem_disk_iff (by decide) 1 b).2 hb.le) hne hprod

end D1Bound5
end
