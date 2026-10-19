-- Prove2me | solution 1 for CohnElkies.tendsto_saddleSmallResidueTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/f3300d8f-1748-44d8-8c41-6a4869fc85c8

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (C : ℝ) :
    Tendsto (saddleSmallResidueTailMajorant C)
      atTop (𝓝 0) := by
  have hneg :
      Tendsto
        (fun ℓ : ℝ =>
          (-(77 / 8 : ℝ)) * Real.log ℓ)
        atTop atBot :=
    Real.tendsto_log_atTop.const_mul_atTop_of_neg
      (by norm_num : (-(77 / 8 : ℝ)) < 0)
  have hsmall :=
    (Real.tendsto_exp_atBot.comp hneg).const_mul
      (Real.exp (3 * C))
  convert! hsmall using 1
  · funext ℓ
    unfold saddleSmallResidueTailMajorant
    rw [show
      3 * C - (77 / 8 : ℝ) * Real.log ℓ =
        3 * C + (-(77 / 8 : ℝ)) * Real.log ℓ by ring,
      Real.exp_add]
    rfl
  · simp
end CohnElkies
