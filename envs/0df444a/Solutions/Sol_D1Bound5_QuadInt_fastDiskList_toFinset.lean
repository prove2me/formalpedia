-- Prove2me | solution 1 for D1Bound5.QuadInt.fastDiskList_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:58.62228+00:00
-- url     : https://prove2.me/submissions/da695d0f-404a-4c65-9827-438455e3c6fc

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FastDiskList_Definitions

section
namespace D1Bound5
namespace QuadInt



theorem mem_fastDiskCoordinates (r z : ℤ) (hr : 0 ≤ r) :
    z ∈ fastDiskCoordinates r ↔ z ∈ Finset.Icc (-r) r := by
  simp only [fastDiskCoordinates, List.mem_map, List.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro hz
    refine ⟨(z+r).toNat, ?_, ?_⟩ <;> omega



/-- A propositional bridge to the existing complete disk enumeration.
The proof does not evaluate a finite set of concrete coordinates. -/
theorem _root_.solution (tau nu M : ℤ) :
    (fastDiskList tau nu M).toFinset = disk tau nu M := by
  have mem_prod (a b : ℤ) (s t : Finset ℤ) :
      (a,b) ∈ s.product t ↔ a ∈ s ∧ b ∈ t := by
    change (a,b) ∈ s ×ˢ t ↔ a ∈ s ∧ b ∈ t
    exact Finset.mem_product
  ext z
  simp only [fastDiskList, disk, List.mem_toFinset, List.mem_map, Prod.exists,
    List.mem_filter, List.mem_product, mem_fastDiskCoordinates _ _ (Int.sqrt_nonneg _), decide_eq_true_eq,
    Finset.mem_image, Finset.mem_filter, mem_prod]

end QuadInt
end D1Bound5
end
