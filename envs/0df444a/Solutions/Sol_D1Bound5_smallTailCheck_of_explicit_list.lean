-- Prove2me | solution 1 for D1Bound5.smallTailCheck_of_explicit_list
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:52.520873+00:00
-- url     : https://prove2.me/submissions/cb2b2912-90d8-43b5-b7e3-8aac7878d896

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
import Definitions.Def_D1Bound5_SmallTailExplicit_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt





/-- The explicit finite list covers the entire mathematical small-tail
statement when it covers the closed disk. The list need not be minimal. -/
theorem _root_.solution {tau nu : ℤ}
    (xs : List (QuadInt tau nu))
    (cover : ∀ z ∈ disk tau nu 15, z ∈ xs)
    (checked : tailListBool xs = true) : SmallTailCheck tau nu := by
  intro b hb c hc h9 hbc hne hsq d hd hd0 hdb hdc hcd
    a ha ha0 hab hac had hNa hsab hsac
  have Hbc := (List.all_eq_true.mp
    ((List.all_eq_true.mp checked) b (cover b hb))) c (cover c hc)
  have Hguard : decide (9 ≤ b.norm ∧ b.norm ≤ c.norm ∧ b ≠ c) = true := by
    simp [h9,hbc,hne]
  have Hp : tailPairBool xs b c = true := by
    simpa only [Hguard,hsq,if_true] using Hbc
  have Hdmem : d ∈ [b+c+2*rootCandidate (b*c+1),b+c-2*rootCandidate (b*c+1)] := by
    simpa using hd
  have Hd := (List.all_eq_true.mp Hp) d Hdmem
  have Hdguard : decide (d ≠ 0 ∧ d ≠ b ∧ d ≠ c ∧ c.norm ≤ d.norm) = true := by
    simp [hd0,hdb,hdc,hcd]
  simp only [Hdguard,if_true] at Hd
  have Ha := (List.all_eq_true.mp Hd) a (cover a ha)
  have Haguard : decide (a ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a.norm ≤ b.norm) = true := by
    simp [ha0,hab,hac,had,hNa]
  cases h : hasSquareRoot (a*d+1) with
  | false => rfl
  | true => simp [Haguard,hsab,hsac,h] at Ha

end D1Bound5
end
