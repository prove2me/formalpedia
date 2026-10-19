-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineGraphMap_graphVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/8cadbf4e-b315-41cd-94a5-4b8e128b977f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLineGraphMap_horizontal
import Theorems.Thm_CompactnessConjecture_symplecticLineGraphMap_symmetric
import Theorems.Thm_CompactnessConjecture_symplecticLineGraphMap_coordinate_expansion

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) :
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm z :
        SymplecticVector K) := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = z := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u = z
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply z
  have hg :
      symplecticLineGraphMap K L hvertical z =
        symplecticVerticalProjection K
          (u : SymplecticVector K) := by
    rw [← hu]
    exact symplecticLineGraphMap_horizontal K L hvertical u
  change
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      (u : SymplecticVector K)
  funext i
  fin_cases i
  · simpa [symmetricGraphVector, symplecticHorizontalProjection]
      using (congrFun hu 0).symm
  · have hg0 := congrFun hg 0
    change
      symplecticLineGraphMap K L hvertical z 0 =
        (u : SymplecticVector K) 1 at hg0
    change
      symplecticLineGraphMap K L hvertical ![1, 0] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 1 =
        (u : SymplecticVector K) 1
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 0).symm.trans hg0
  · simpa [symmetricGraphVector, symplecticHorizontalProjection]
      using (congrFun hu 1).symm
  · have hg1 := congrFun hg 1
    change
      symplecticLineGraphMap K L hvertical z 1 =
        (u : SymplecticVector K) 3 at hg1
    change
      symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 1 * z 1 =
        (u : SymplecticVector K) 3
    rw [← symplecticLineGraphMap_symmetric K L hvertical]
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 1).symm.trans hg1
end CompactnessConjecture
