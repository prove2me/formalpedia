-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_le_center_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/ac13cd70-99f6-4107-8002-cb6c72a5b5cf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      (1 / (1 - Real.cos (stripAngle σ))) *
        stripPoissonKernel 0 T := by
  let A : ℝ := Real.cosh (Real.pi * T / 2)
  let q : ℝ := Real.cos (stripAngle σ)
  let c : ℝ := 1 - q
  have hangle := stripAngle_mem_Ioo hbelow
    (show σ < 1 by linarith)
  have hhalf : stripAngle σ ≤ Real.pi / 2 := by
    unfold stripAngle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      Real.pi_pos.le hnonpos]
  have hq : 0 ≤ q := by
    try dsimp [q]
    apply Real.cos_nonneg_of_mem_Icc
    exact ⟨by linarith [Real.pi_pos], hhalf⟩
  have hqlt : q < 1 := by
    try dsimp [q]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle.2.le hangle.1
    simpa using! h
  have hc : 0 < c := by
    try dsimp [c]
    linarith
  have hA : 0 < A := Real.cosh_pos _
  have hAone : 1 ≤ A := Real.one_le_cosh _
  have hcompare : c * A ≤ A - q := by
    try dsimp [c]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hAone)]
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  have hcA : 0 < 4 * (c * A) := by positivity
  calc
    stripPoissonKernel σ T =
        Real.sin (stripAngle σ) / (4 * (A - q)) := rfl
    _ ≤ Real.sin (stripAngle σ) / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_left hsin.le hcA
      exact mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ ≤ 1 / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_right
        (Real.sin_le_one (stripAngle σ)) hcA.le
    _ = (1 / (1 - Real.cos (stripAngle σ))) *
          stripPoissonKernel 0 T := by
      have hcenter : stripPoissonKernel 0 T =
          1 / (4 * A) := by
        simp [stripPoissonKernel, stripAngle, A]
      rw [hcenter]
      change 1 / (4 * (c * A)) =
        (1 / c) * (1 / (4 * A))
      field_simp [hc.ne', hA.ne']
end CohnElkies
