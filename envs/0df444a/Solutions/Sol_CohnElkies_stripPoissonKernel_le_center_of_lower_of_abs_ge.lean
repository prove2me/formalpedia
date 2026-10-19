-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_le_center_of_lower_of_abs_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/e5f46858-8a2b-4977-b7f7-b51b3a23164a

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
    {σ δ T : ℝ}
    (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    (hδ : 0 < δ) (hT : δ ≤ |T|) :
    stripPoissonKernel σ T ≤
      (1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)) *
        stripPoissonKernel 0 T := by
  let A : ℝ := Real.cosh (Real.pi * T / 2)
  let C : ℝ := Real.cosh (Real.pi * δ / 2)
  let c : ℝ := 1 - C⁻¹
  have hδarg : Real.pi * δ / 2 ≠ 0 := by
    exact (div_pos (mul_pos Real.pi_pos hδ)
      (by norm_num)).ne'
  have hC : 1 < C := by
    exact Real.one_lt_cosh.mpr hδarg
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have hc : 0 < c := by
    try dsimp [c]
    have hrecip : C⁻¹ < 1 := (inv_lt_one₀ hCpos).mpr hC
    linarith
  have hA : 0 < A := Real.cosh_pos _
  have hCA : C ≤ A := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div, abs_div, abs_mul, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos hδ]
    norm_num
    gcongr
  have hratio : 1 ≤ A / C := by
    apply (le_div_iff₀ hCpos).2
    simpa using! hCA
  have hangle := stripAngle_mem_Ioo hbelow
    (show σ < 1 by linarith)
  have hcoslt : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle.2.le hangle.1
    simpa using! h
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  have hden : 0 < A - Real.cos (stripAngle σ) := by
    try dsimp [A]
    linarith [Real.one_le_cosh (Real.pi * T / 2)]
  have hcompare : c * A ≤ A - Real.cos (stripAngle σ) := by
    have hcos := Real.cos_le_one (stripAngle σ)
    try dsimp [c]
    rw [sub_mul, one_mul, inv_mul_eq_div]
    linarith
  have hcA : 0 < 4 * (c * A) := by positivity
  calc
    stripPoissonKernel σ T =
        Real.sin (stripAngle σ) /
          (4 * (A - Real.cos (stripAngle σ))) := rfl
    _ ≤ Real.sin (stripAngle σ) / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_left hsin.le hcA
      exact mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ ≤ 1 / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_right
        (Real.sin_le_one (stripAngle σ)) hcA.le
    _ = (1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)) *
          stripPoissonKernel 0 T := by
      simp only [stripPoissonKernel, stripAngle]
      norm_num
      try dsimp [A, C, c]
      field_simp [hc.ne', hA.ne']
end CohnElkies
