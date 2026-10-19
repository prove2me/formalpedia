-- Prove2me | solution 1 for CohnElkies.tendsto_saddleFirstBranchTailLogMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/22973418-cfe2-40a2-bfce-606da45c9237

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    Tendsto (saddleFirstBranchTailLogMajorant c C)
      atTop (𝓝 (0 : ℝ)) := by
  have hx : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / 4)
      atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const
      (by norm_num : (0 : ℝ) < 4)
  have hpower : Tendsto
      (fun ℓ : ℝ =>
        (Real.log ℓ / 4) ^ (1 / 6 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 6)).comp hx
  have hrate : 0 < c / (4 * C) := by positivity
  have hnegative : Tendsto
      (fun ℓ : ℝ =>
        -(c / (4 * C)) *
          (Real.log ℓ / 4) ^ (1 / 6 : ℝ))
      atTop atBot :=
    hpower.const_mul_atTop_of_neg (by linarith)
  have hexp : Tendsto
      (fun ℓ : ℝ =>
        Real.exp
          (-(c / (4 * C)) *
            (Real.log ℓ / 4) ^ (1 / 6 : ℝ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hratio : Tendsto
      (fun ℓ : ℝ => C / (Real.log ℓ / 4))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hx
  have hsqrt : Tendsto
      (fun ℓ : ℝ =>
        Real.sqrt (C / (Real.log ℓ / 4)))
      atTop (𝓝 (0 : ℝ)) := by
    convert! hratio.sqrt using 1; simp
  have hfirst := hexp.const_mul
    (4 * Real.sqrt (Real.pi * C / c))
  have hsecond := hsqrt.const_mul (16 / c)
  change Tendsto
    (fun ℓ : ℝ =>
      4 * Real.sqrt (Real.pi * C / c) *
          Real.exp
            (-(c / (4 * C)) *
              (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) +
        (16 / c) *
          Real.sqrt (C / (Real.log ℓ / 4)))
    atTop (𝓝 (0 : ℝ))
  simpa using! hfirst.add hsecond
end CohnElkies
