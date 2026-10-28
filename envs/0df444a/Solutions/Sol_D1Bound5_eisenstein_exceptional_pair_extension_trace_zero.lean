-- Prove2me | solution 1 for D1Bound5.eisenstein_exceptional_pair_extension_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:18:50.849401+00:00
-- url     : https://prove2.me/submissions/be5d059e-2bbd-46e4-b438-831a32cc6f3a

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
import Theorems.Thm_D1Bound5_eisenstein_sum_squares_balanced_coordinates

section
namespace D1Bound5
open QuadInt

/-- Every common extension of the exceptional Eisenstein unit pair
(-ω,1-ω), whose product is -1, has zero trace. No bound on the extension
or on its square roots is assumed. -/
theorem _root_.solution
    (z : QuadInt 1 1)
    (hr : ∃ r : QuadInt 1 1, r*r = (⟨0,-1⟩ : QuadInt 1 1)*z+1)
    (hs : ∃ s : QuadInt 1 1, s*s = (⟨1,-1⟩ : QuadInt 1 1)*z+1) :
    2*z.re+z.im = 0 := by
  obtain ⟨r,hr⟩ := hr
  obtain ⟨s,hs⟩ := hs
  have hrR := congrArg (fun w : QuadInt 1 1 => w.re) hr
  have hrI := congrArg (fun w : QuadInt 1 1 => w.im) hr
  have hsR := congrArg (fun w : QuadInt 1 1 => w.re) hs
  have hsI := congrArg (fun w : QuadInt 1 1 => w.im) hs
  norm_num [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hrR hrI hsR hsI
  have hR : r.re^2-r.im^2+s.im^2-(-s.re-s.im)^2 = 0 := by
    nlinarith only [hrR, hsR, hsI]
  have hI : 2*r.re*r.im+r.im^2+2*s.im*(-s.re-s.im)+(-s.re-s.im)^2 = 1 := by
    nlinarith only [hrI, hsR]
  rcases eisenstein_sum_squares_balanced_coordinates
    r.re r.im s.im (-s.re-s.im) hR hI with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hsre : s.re = -r.re-r.im := by omega
    rw [hsre, h1] at hsI
    nlinarith only [hrI, hsI]
  · have hsre : s.re = r.re+r.im := by omega
    rw [hsre, h1] at hsI
    nlinarith only [hrI, hsI]

end D1Bound5
end
