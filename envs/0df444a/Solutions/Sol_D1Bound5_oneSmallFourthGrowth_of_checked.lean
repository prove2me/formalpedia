-- Prove2me | solution 1 for D1Bound5.oneSmallFourthGrowth_of_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:54:05.928978+00:00
-- url     : https://prove2.me/submissions/9b78c7ef-4e7c-4154-a3b7-8ea5edfcc8c9

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff
import Theorems.Thm_D1Bound5_one_small_fourth_root_norm_le
import Theorems.Thm_D1Bound5_pairSeedCandidate_eq

section
namespace D1Bound5
open QuadInt





















theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b s : QuadInt tau nu)
    (ha : a ≠ 0) (hNa : a.norm ≤ 2) (cutoff : ℤ) (hcutoff : cutoff ≤ 21270)
    (roots : List (QuadInt tau nu))
    (hcover : ∀ q ∈ disk tau nu 300, q ∈ roots)
    (hcheck : oneSmallFourthGrowthBool a b s cutoff roots = true)
    (z : QuadInt tau nu) (hz : z.norm < cutoff)
    (hza : ∃ q, q*q = a*z+1) (hzb : ∃ q, q*q = b*z+1)
    (hzs : ∃ q, q*q = s*z+1) : z.norm ≤ 4*b.norm*s.norm := by
  obtain ⟨q,hq⟩ := hza
  have hNq := one_small_fourth_root_norm_le hd a z q hNa (by omega) hq
  have hmq := hcover q ((mem_disk_iff hd 300 q).2 hNq)
  have hc := List.all_eq_true.mp hcheck q hmq
  have heq := pairSeedCandidate_eq hd a z q ha hq
  have hrb := (hasSquareRoot_iff hd _).2 hzb
  have hrs := (hasSquareRoot_iff hd _).2 hzs
  simpa [heq, hq, hz, hrb, hrs] using hc

end D1Bound5
end
