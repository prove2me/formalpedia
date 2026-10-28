-- Prove2me | solution 1 for D1Bound5.mutate_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:24:00.504154+00:00
-- url     : https://prove2.me/submissions/37d73ac5-f90f-4742-afd2-ae33b71dea8c

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions

section
namespace D1Bound5



/-- The transformed roots remain integral without any division. -/
theorem _root_.solution {R : Type*} [CommRing R] (a b z r0 r s : R)
    (h0 : r0^2 = a*b+1) (hr : r^2 = a*z+1) (hs : s^2 = b*z+1) :
    (r0*r+a*s)^2 = a*mutate a b z r0 r s+1 ∧
    (b*r+r0*s)^2 = b*mutate a b z r0 r s+1 := by
  unfold mutate
  constructor
  · linear_combination r^2*h0 + (a*b+1)*hr + a^2*hs
  · linear_combination s^2*h0 + b^2*hr + (a*b+1)*hs





end D1Bound5
end
