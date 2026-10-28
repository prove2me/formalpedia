-- Prove2me | solution 1 for D1Bound5.mutate_reverse_canonical
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:43.926823+00:00
-- url     : https://prove2.me/submissions/4677d891-6780-4a2e-9e4e-5c6bc46a4fcb

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
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_mutate_eq_canonical
import Theorems.Thm_D1Bound5_mutate_roots

section
namespace D1Bound5





/-- The inverse transformation recovers the extension. No nonzero hypothesis
is made on a root, on the extension, or on a transformed value. -/
theorem mutate_reverse {R : Type*} [CommRing R] (a b z r0 r s : R)
    (h0 : r0^2 = a*b+1) (hr : r^2 = a*z+1) (hs : s^2 = b*z+1) :
    a+b+(2*a*b+1)*mutate a b z r0 r s -
      2*r0*(r0*r+a*s)*(b*r+r0*s) = z := by
  unfold mutate
  linear_combination (-2*a*s^2-2*b*r^2-2*r*r0*s)*h0 +
    (-2*a*b^2-2*b)*hr + (-2*a^2*b-2*a)*hs



end D1Bound5
end

section
namespace D1Bound5
open QuadInt

























/-- Every mutation edge can be reversed using one of the two canonical
neighbors of its target, regardless of the original root signs. -/
theorem _root_.solution {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (a b z r0 r s : QuadInt tau nu)
    (h0 : r0*r0 = a*b+1) (hr : r*r = a*z+1) (hs : s*s = b*z+1) :
    z = pairMutationPlus a b (mutate a b z r0 r s) ∨
    z = pairMutationMinus a b (mutate a b z r0 r s) := by
  have h0' : r0^2 = a*b+1 := by simpa only [pow_two] using h0
  have hr' : r^2 = a*z+1 := by simpa only [pow_two] using hr
  have hs' : s^2 = b*z+1 := by simpa only [pow_two] using hs
  have hroots := mutate_roots a b z r0 r s h0' hr' hs'
  have hp : (r0*r+a*s)*(r0*r+a*s) = a*mutate a b z r0 r s+1 := by
    simpa only [pow_two] using hroots.1
  have hq : (-(b*r+r0*s))*(-(b*r+r0*s)) = b*mutate a b z r0 r s+1 := by
    simpa only [neg_mul_neg, pow_two] using hroots.2
  have hrev : mutate a b (mutate a b z r0 r s) r0
      (r0*r+a*s) (-(b*r+r0*s)) = z := by
    have h := mutate_reverse a b z r0 r s h0' hr' hs'
    unfold mutate at h ⊢
    linear_combination h
  have hcases := mutate_eq_canonical hd a b (mutate a b z r0 r s)
    r0 (r0*r+a*s) (-(b*r+r0*s)) h0 hp hq
  rwa [hrev] at hcases









end D1Bound5
end
