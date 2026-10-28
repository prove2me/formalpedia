-- Prove2me | solution 1 for D1Bound5.pairSeedsCovered_of_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:34.430051+00:00
-- url     : https://prove2.me/submissions/3fbb87df-05b3-4f8e-9ebf-5ecb5cf2c44e

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff
import Theorems.Thm_D1Bound5_pairSeedCandidate_eq
import Theorems.Thm_D1Bound5_pair_seed_root_norm_le

section
namespace D1Bound5
open QuadInt













/-- Mathematical soundness of the root-based finite seed certificate. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hNa : a.norm ≤ 8)
    (roots vertices : List (QuadInt tau nu))
    (hcover : ∀ q ∈ disk tau nu 132, q ∈ roots)
    (hcheck : pairSeedsCoveredBool a b roots vertices = true)
    (z : QuadInt tau nu) (hz : PairExtension a b z) (hNz : z.norm ≤ 1089) :
    z ∈ vertices := by
  obtain ⟨⟨q, hq⟩, hs⟩ := hz
  have hNq := pair_seed_root_norm_le hd a z q hNa hNz hq
  have hmem := hcover q ((mem_disk_iff hd 132 q).2 hNq)
  have hc := List.all_eq_true.mp hcheck q hmem
  have heq := pairSeedCandidate_eq hd a z q ha hq
  have hb := (hasSquareRoot_iff hd _).2 hs
  simpa [heq, hq, hNz, hb] using hc





















end D1Bound5
end
