-- Prove2me | solution 1 for D1Bound5.one_three_im_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:17.65879+00:00
-- url     : https://prove2.me/submissions/391ab3fc-246c-4acf-98bb-a32d0b5b0396

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_three_le_discriminant
import Theorems.Thm_D1Bound5_one_three_integer_obstruction

section
namespace D1Bound5






/-- Every common extension of 1 and 3 has zero imaginary coordinate.
This theorem is over the exact quadratic-coordinate model; the global
full-ring bridge is not assumed or supplied by this declaration. -/
theorem _root_.solution (tau nu : ℤ)
    (hd : 0 < QuadInt.discriminant tau nu)
    {z r s : QuadInt tau nu} (hr : r*r = z+1) (hs : s*s = 3*z+1) :
    z.im = 0 := by
  by_contra hz
  have hrI : 2*r.re*r.im+tau*r.im*r.im = z.im := by
    have hi := congrArg (fun q : QuadInt tau nu => q.im) hr
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add,
      QuadraticAlgebra.im_one, add_zero] at hi
    nlinarith [hi]
  have hsI : 2*s.re*s.im+tau*s.im*s.im = 3*z.im := by
    have hi := congrArg (fun q : QuadInt tau nu => q.im) hs
    simp [QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat] at hi
    nlinarith [hi]
  have hrR : r.re*r.re-nu*r.im*r.im = z.re+1 := by
    have he := congrArg (fun q : QuadInt tau nu => q.re) hr
    simpa only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
      QuadraticAlgebra.re_one, neg_mul, sub_eq_add_neg] using he
  have hsR : s.re*s.re-nu*s.im*s.im = 3*z.re+1 := by
    have he := congrArg (fun q : QuadInt tau nu => q.re) hs
    simpa [QuadraticAlgebra.re_one, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, neg_mul, sub_eq_add_neg] using he
  let e := 2*r.re+tau*r.im
  let f := r.im
  let g := 2*s.re+tau*s.im
  let h := s.im
  let k := r.re*s.im-r.im*s.re
  have heq : e*f = z.im := by dsimp [e,f]; nlinarith [hrI]
  have hgeq : g*h = 3*z.im := by dsimp [g,h]; nlinarith [hsI]
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, mul_zero] at heq
    exact hz heq.symm
  have hg : g ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at hgeq
    omega
  have him : g*h = 3*e*f := by nlinarith [heq, hgeq]
  have hre : 3*e^2-g^2+QuadInt.discriminant tau nu*(h^2-3*f^2) = 8 := by
    dsimp [e,f,g,h,QuadInt.discriminant]
    linear_combination 12*hrR-4*hsR+6*tau*hrI-2*tau*hsI
  have hk : e*h-f*g = 2*k := by dsimp [e,f,g,h,k]; ring
  exact one_three_integer_obstruction (QuadInt.discriminant tau nu) e f g h k
    (QuadInt.three_le_discriminant hd) hf hg him hre hk



end D1Bound5
end
