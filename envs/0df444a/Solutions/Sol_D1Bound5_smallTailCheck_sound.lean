-- Prove2me | solution 1 for D1Bound5.smallTailCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:45.065656+00:00
-- url     : https://prove2.me/submissions/882dd93d-a83c-40fe-839c-480ca5f8605a

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FiniteTail_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff
import Theorems.Thm_D1Bound5_QuadInt_rootCandidate_complete
import Theorems.Thm_D1Bound5_regular_completion_cases

section
namespace D1Bound5

open QuadInt







/-- A checked finite tail excludes every quadruple covered by its norm
bounds. This theorem proves the enumeration and edge-coverage implication. -/
theorem _root_.solution {tau nu : ℤ} (hd : 0 < QuadInt.discriminant tau nu)
    (check : SmallTailCheck tau nu) (a b c d : QuadInt tau nu)
    (ha0 : a ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hdb : d ≠ b) (hdc : d ≠ c)
    (hNa : a.norm ≤ b.norm) (hNb : 9 ≤ b.norm)
    (hNbc : b.norm ≤ c.norm) (hNc : c.norm ≤ 15) (hNcd : c.norm ≤ d.norm)
    (hsbc : ∃ r, r*r = b*c+1) (hsab : ∃ r, r*r = a*b+1)
    (hsac : ∃ r, r*r = a*c+1) (hsad : ∃ r, r*r = a*d+1)
    (hreg : regularDefect b c d = 0) : False := by
  have hbmem := (mem_disk_iff hd 15 b).mpr (hNbc.trans hNc)
  have hcmem := (mem_disk_iff hd 15 c).mpr hNc
  have hamem := (mem_disk_iff hd 15 a).mpr (hNa.trans (hNbc.trans hNc))
  have hcheck := check b hbmem c hcmem hNb hNbc hbc
    ((hasSquareRoot_iff hd _).mpr hsbc)
  have hrc := rootCandidate_complete hd hsbc
  have hdmem : d ∈ ({b+c+2*rootCandidate (b*c+1),b+c-2*rootCandidate (b*c+1)} :
      Finset (QuadInt tau nu)) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      regular_completion_cases hd b c d (rootCandidate (b*c+1)) hrc hreg
  have hfalse := hcheck d hdmem hd0 hdb hdc hNcd a hamem ha0 hab hac had hNa
    ((hasSquareRoot_iff hd _).mpr hsab) ((hasSquareRoot_iff hd _).mpr hsac)
  have htrue := (hasSquareRoot_iff hd _).mpr hsad
  rw [htrue] at hfalse
  contradiction






end D1Bound5
end
