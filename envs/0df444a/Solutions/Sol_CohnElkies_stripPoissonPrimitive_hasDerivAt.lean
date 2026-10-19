-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/ee339819-5146-40d4-9ed8-18cc959317ee

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    HasDerivAt (stripPoissonPrimitive σ)
      (stripPoissonKernel σ T) T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hsin0 : Real.sin (stripAngle σ) ≠ 0 := hsin.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hexp : 0 < Real.exp (Real.pi * T / 2) := Real.exp_pos _
  have hderiv :
      HasDerivAt
        (fun x : ℝ =>
          (Real.exp (Real.pi * x / 2) - Real.cos (stripAngle σ)) /
            Real.sin (stripAngle σ))
        ((Real.exp (Real.pi * T / 2) * (Real.pi / 2)) /
          Real.sin (stripAngle σ)) T := by
    convert!
      (((Real.hasDerivAt_exp (Real.pi * T / 2)).comp T
        ((hasDerivAt_id T).const_mul Real.pi |>.div_const 2)).sub_const
        (Real.cos (stripAngle σ))).div_const (Real.sin (stripAngle σ)) using 1
    all_goals simp [mul_comm]
  convert!
    ((Real.hasDerivAt_arctan _).comp T hderiv).div_const Real.pi
      using 1
  unfold stripPoissonKernel
  rw [Real.cosh_eq, Real.exp_neg]
  have htrig := Real.sin_sq_add_cos_sq (stripAngle σ)
  have hden : 0 <
      Real.exp (Real.pi * T / 2) ^ 2 + 1 -
        2 * Real.exp (Real.pi * T / 2) * Real.cos (stripAngle σ) := by
    nlinarith [sq_nonneg
      (Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)),
      sq_pos_of_pos hsin]
  field_simp [hsin0, hpi, hexp.ne', hden.ne']
  nlinarith
end CohnElkies
