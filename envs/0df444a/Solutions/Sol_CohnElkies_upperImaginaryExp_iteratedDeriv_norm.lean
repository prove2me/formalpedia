-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_iteratedDeriv_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/6b6b80d5-413c-4416-9aa6-026d43331a0d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_iteratedDeriv
import Theorems.Thm_CohnElkies_upperImaginaryExp_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n upperImaginaryExp x‖ = 1 := by
  rw [upperImaginaryExp_iteratedDeriv,
    norm_mul, norm_pow, upperImaginaryExp_norm]
  simp
end CohnElkies
