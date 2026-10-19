-- Prove2me | solution 1 for CohnElkies.tendsto_saddleSourceSecondBranchLocalTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/6d351406-2e45-4811-865f-f6af53b977dc

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto
      (fun ℓ : ℝ =>
        2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
          Real.exp
            (-(ℓ ^ (1 / 6 : ℝ) /
              (400 * Real.exp 1))))
      atTop (𝓝 (0 : ℝ)) := by
  have hpower : Tendsto
      (fun ℓ : ℝ => ℓ ^ (1 / 6 : ℝ))
      atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hnegative : Tendsto
      (fun ℓ : ℝ =>
        (-(1 / (400 * Real.exp 1))) *
          ℓ ^ (1 / 6 : ℝ))
      atTop atBot :=
    hpower.const_mul_atTop_of_neg
      (neg_lt_zero.mpr
        (by positivity : (0 : ℝ) < 1 / (400 * Real.exp 1)))
  have hexp := Real.tendsto_exp_atBot.comp hnegative
  have hscaled := hexp.const_mul
    (2 * Real.sqrt (400 * Real.exp 1 * Real.pi))
  convert! hscaled using 1
  · funext ℓ
    congr 2
    ring
  · simp
end CohnElkies
