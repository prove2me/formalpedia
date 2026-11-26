-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.mono_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:48.222383+00:00
-- url     : https://prove2.me/submissions/b919420b-35d1-4047-afc1-8e368a901a46

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace PowerDense
theorem _root_.solution {S : Set ℕ} {C C' D : ℝ}
    (h : PowerDense S C D) (hCC' : C ≤ C') :
    PowerDense S C' D := by
  refine ⟨lt_of_lt_of_le h.C_pos hCC', h.D_pos, h.D_le_one, ?_⟩
  intro X hX
  exact (h.bad_bound X hX).trans
    (mul_le_mul_of_nonneg_right hCC'
      (Real.rpow_nonneg (by positivity) _))
end PowerDense
end FirstPassageLinearTransport
