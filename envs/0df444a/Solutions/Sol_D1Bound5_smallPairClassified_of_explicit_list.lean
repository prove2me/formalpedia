-- Prove2me | solution 1 for D1Bound5.smallPairClassified_of_explicit_list
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:16.663432+00:00
-- url     : https://prove2.me/submissions/f714d2ed-1fa2-405f-91b6-7cecb713901b

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff

section
namespace D1Bound5
open QuadInt





theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (xs : List (QuadInt tau nu))
    (rows : List (Finset (ℤ × ℤ)))
    (cover : ∀ z ∈ disk tau nu 8, z ∈ xs)
    (checked : smallPairClassifiedBool xs rows = true)
    (a b : QuadInt tau nu) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hroot : ∃ r, r*r = a*b+1) (hnondeg : a*b+1 ≠ 0)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8) : pairCoordinates a b ∈ rows := by
  have hma := cover a ((mem_disk_iff hd 8 a).2 hNa)
  have hmb := cover b ((mem_disk_iff hd 8 b).2 hNb)
  have Ha := List.all_eq_true.mp checked a hma
  have ga : decide (a ≠ 0) = true := by simp [ha]
  simp only [ga, if_true] at Ha
  have Hb := List.all_eq_true.mp Ha b hmb
  have gb : decide (b ≠ 0 ∧ a ≠ b ∧ a*b+1 ≠ 0) = true := by
    simp [hb, hab, hnondeg]
  have hs := (hasSquareRoot_iff hd _).2 hroot
  simpa [gb, hs] using Hb

end D1Bound5
end
