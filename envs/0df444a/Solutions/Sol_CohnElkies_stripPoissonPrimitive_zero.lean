-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/88833fe1-bb87-4b2c-a703-73e0f1b2a7f4

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
    (hbelow : -1 < σ) (habove : σ < 1) :
    stripPoissonPrimitive σ 0 = stripAngle σ / (2 * Real.pi) := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hhalf : 0 < stripAngle σ / 2 := half_pos hangle
  have hhalf' : stripAngle σ / 2 < Real.pi / 2 := by linarith
  have hcos : 0 < Real.cos (stripAngle σ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf'⟩
  have hsin : 0 < Real.sin (stripAngle σ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf (by linarith [Real.pi_pos])
  have hratio :
      (1 - Real.cos (stripAngle σ)) / Real.sin (stripAngle σ) =
        Real.tan (stripAngle σ / 2) := by
    conv_lhs =>
      arg 1
      arg 2
      rw [show stripAngle σ = 2 * (stripAngle σ / 2) by ring,
        Real.cos_two_mul_eq_one_sub]
    conv_lhs =>
      arg 2
      rw [show stripAngle σ = 2 * (stripAngle σ / 2) by ring,
        Real.sin_two_mul]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hsin.ne', hcos.ne']
    ring
  unfold stripPoissonPrimitive
  simp only [mul_zero, zero_div, Real.exp_zero]
  rw [hratio, Real.arctan_tan (by linarith [Real.pi_pos]) hhalf']
  ring
end CohnElkies
