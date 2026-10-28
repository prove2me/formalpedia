-- Prove2me | solution 1 for D1Bound5.irregular_extensions_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:56:55.672954+00:00
-- url     : https://prove2.me/submissions/f3af518d-478d-4cd1-a57d-c24f7cac2daf

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_extension_product

section
namespace D1Bound5









/-- Irregularity makes both algebraic extensions nonzero. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (a b c r s t : R) (hr : r^2 = a*b+1) (hs : s^2 = a*c+1)
    (ht : t^2 = b*c+1) (hi : regularDefect a b c ≠ 0) :
    a+b+c+2*a*b*c+2*r*s*t ≠ 0 ∧ a+b+c+2*a*b*c-2*r*s*t ≠ 0 := by
  have h := extension_product a b c r s t hr hs ht
  constructor
  · intro hz
    apply hi
    rw [hz, zero_mul] at h
    exact h.symm
  · intro hz
    apply hi
    rw [hz, mul_zero] at h
    exact h.symm

end D1Bound5
end
