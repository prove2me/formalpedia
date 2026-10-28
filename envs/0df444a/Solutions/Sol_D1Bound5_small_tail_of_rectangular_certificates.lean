-- Prove2me | solution 1 for D1Bound5.small_tail_of_rectangular_certificates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:45.879398+00:00
-- url     : https://prove2.me/submissions/7374968b-a420-4b9e-9c26-825fd3b98079

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteTail_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_smallTailCheck_sound
import Theorems.Thm_D1Bound5_small_tail_discriminant_bound
import Theorems.Thm_D1Bound5_small_tail_parameter_range

section
namespace D1Bound5



/-- A complete checker for the 30-element parameter rectangle suffices
for the small-tail regular-completion obstruction. The finite Boolean
certificates are separate, still-open obligations. -/
theorem _root_.solution
    (certificate : ∀ tau nu : ℤ,
      (tau = 0 ∨ tau = 1) →
      1 ≤ nu → nu ≤ 15 →
      0 < QuadInt.discriminant tau nu →
      SmallTailCheck tau nu)
    {tau nu : ℤ} (htau : tau = 0 ∨ tau = 1)
    (hpos : 0 < QuadInt.discriminant tau nu)
    (a b c d : QuadInt tau nu)
    (ha0 : a ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hdb : d ≠ b) (hdc : d ≠ c)
    (hNa : a.norm ≤ b.norm) (hNb : 9 ≤ b.norm)
    (hNbc : b.norm ≤ c.norm) (hNc : c.norm ≤ 15) (hNcd : c.norm ≤ d.norm)
    (hsbc : ∃ r, r*r = b*c+1) (hsab : ∃ r, r*r = a*b+1)
    (hsac : ∃ r, r*r = a*c+1) (hsad : ∃ r, r*r = a*d+1)
    (hreg : regularDefect b c d = 0) : False := by
  obtain ⟨r,hr⟩ := hsbc
  have hdiscr := small_tail_discriminant_bound hpos b c r hbc hNb hNbc hNc hr
  obtain ⟨hlo,hhi⟩ := small_tail_parameter_range tau nu htau hpos hdiscr
  exact smallTailCheck_sound hpos (certificate tau nu htau hlo hhi hpos)
    a b c d ha0 hd0 hab hac had hbc hdb hdc
    hNa hNb hNbc hNc hNcd ⟨r,hr⟩ hsab hsac hsad hreg

end D1Bound5
end
