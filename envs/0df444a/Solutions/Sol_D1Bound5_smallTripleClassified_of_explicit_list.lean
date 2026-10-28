-- Prove2me | solution 1 for D1Bound5.smallTripleClassified_of_explicit_list
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:17.493298+00:00
-- url     : https://prove2.me/submissions/5f421506-0a4a-4d32-9ce0-8cb4f101d535

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff

section
namespace D1Bound5
open QuadInt





/-- Soundness of the complete small-triple classifier. -/
theorem _root_.solution {tau nu : ℤ}
    (hpos : 0 < discriminant tau nu)
    (xs : List (QuadInt tau nu)) (rows : List (Finset (ℤ × ℤ)))
    (cover : ∀ z ∈ disk tau nu 8, z ∈ xs)
    (checked : smallTripleClassifiedBool xs rows = true)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ rows := by
  have hmem (i : Fin 3) : t i ∈ xs :=
    cover (t i) ((mem_disk_iff hpos 8 (t i)).2 (hnorm i))
  have hne (i j : Fin 3) (hij : i ≠ j) : t i ≠ t j :=
    fun h => hij (ht.1 h)
  have hs (i j : Fin 3) (hij : i ≠ j) :
      hasSquareRoot (t i*t j+1) = true :=
    (hasSquareRoot_iff hpos _).2 (ht.2.2 i j hij)
  have Ha := List.all_eq_true.mp checked (t 0) (hmem 0)
  have ga : decide (t 0 ≠ 0) = true := by simp [ht.2.1 0]
  simp only [ga, if_true] at Ha
  have Hb := List.all_eq_true.mp Ha (t 1) (hmem 1)
  have gb : decide (t 1 ≠ 0 ∧ t 0 ≠ t 1) = true := by
    simp [ht.2.1 1, hne 0 1 (by decide)]
  have hs01 := hs 0 1 (by decide)
  simp only [gb, hs01, if_true] at Hb
  have Hc := List.all_eq_true.mp Hb (t 2) (hmem 2)
  have gc : decide (t 2 ≠ 0 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2) = true := by
    simp [ht.2.1 2, hne 0 2 (by decide), hne 1 2 (by decide)]
  have hs02 := hs 0 2 (by decide)
  have hs12 := hs 1 2 (by decide)
  simpa [gc, hs02, hs12] using Hc

end D1Bound5
end
