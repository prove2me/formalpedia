-- Prove2me | solution 1 for D1Bound5.QuadInt.exists_normalized_root
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:35.940836+00:00
-- url     : https://prove2.me/submissions/b9652bea-e4ba-41e2-9104-6841975fa8df

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}



/-- A square root can be given nonnegative doubled real part; if that part
is zero, its second coordinate may also be chosen nonnegative. -/
theorem _root_.solution {z : QuadInt tau nu} (hz : ∃ r, r*r = z) :
    ∃ r : QuadInt tau nu, r*r = z ∧ 0 ≤ 2*r.re+tau*r.im ∧
      (2*r.re+tau*r.im = 0 → 0 ≤ r.im) := by
  obtain ⟨r, hr⟩ := hz
  by_cases he : 0 ≤ 2*r.re+tau*r.im
  · by_cases he0 : 2*r.re+tau*r.im = 0
    · by_cases hi : 0 ≤ r.im
      · exact ⟨r, hr, he, fun _ => hi⟩
      · refine ⟨-r, by simpa only [neg_mul_neg] using hr, ?_, ?_⟩
        · change 0 ≤ 2*(-r.re)+tau*(-r.im)
          nlinarith only [he0]
        · intro _
          change 0 ≤ -r.im
          omega
    · exact ⟨r, hr, he, fun h => False.elim (he0 h)⟩
  · refine ⟨-r, by simpa only [neg_mul_neg] using hr, ?_, ?_⟩
    · change 0 ≤ 2*(-r.re)+tau*(-r.im)
      nlinarith
    · intro h
      change 2*(-r.re)+tau*(-r.im) = 0 at h
      exfalso
      nlinarith





















end D1Bound5.QuadInt
end
