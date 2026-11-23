-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_exclusion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:59.147231+00:00
-- url     : https://prove2.me/submissions/dcc0dbee-1b94-467c-afb6-9e318eefe88e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_affine_log_le_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : ExclusionInequalities := by
  intro ε A hε hA
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_affine_log_le_rpow ε (Real.log 20) (3 * A) (2 / 5) hε (by norm_num)).and
      ((eventually_le_rpow ε (Real.log 3 * (5 / 4)) hε).and (eventually_ge_atTop (1 : ℝ))))
  refine ⟨x₀, fun x hx r Y hr hY => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set L : ℝ := x ^ ε with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos hx0 _
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hl8 : 8 * L ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).mpr hY
  have hY1 : 1 ≤ Y := by
    refine le_trans ?_ hY
    exact Real.one_le_exp (by positivity)
  set R : ℝ := x ^ A with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow e3 hA.le
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hY34 : 1 ≤ Y ^ (3 / 4 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have hY45 : 1 ≤ Y ^ (4 / 5 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have s1 : Y ^ (4 / 5 : ℝ) = Y ^ (3 / 4 : ℝ) * Y ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have s2 : Y ^ (9 / 10 : ℝ) = Y ^ (4 / 5 : ℝ) * Y ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have t1 : 20 * R ^ 3 ≤ Y ^ (1 / 20 : ℝ) := by
    have u1 : 20 * R ^ 3 = Real.exp (Real.log 20 + 3 * A * Real.log x) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), hR, Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    rw [u1, Real.rpow_def_of_pos hY0]
    exact Real.exp_le_exp.mpr (by linarith)
  have t2 : 3 ≤ Y ^ (1 / 10 : ℝ) := by
    rw [Real.rpow_def_of_pos hY0]
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log Y * (1 / 10)) := Real.exp_le_exp.mpr (by linarith)
  constructor
  · have a1 : 3 * (r : ℝ) + 1 ≤ 4 * R := by linarith
    have hr2 : (r : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr0 hr 2
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
    have a2 : 4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) + 1 ≤ 5 * R ^ 2 * Y ^ (3 / 4 : ℝ) := by
      have v1 : 4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) ≤ 4 * R ^ 2 * Y ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have v2 : 1 ≤ R ^ 2 * Y ^ (3 / 4 : ℝ) := one_le_mul_of_one_le_of_one_le hR2 hY34
      linarith
    calc (3 * (r : ℝ) + 1) * (4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) + 1)
        ≤ (4 * R) * (5 * R ^ 2 * Y ^ (3 / 4 : ℝ)) := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = Y ^ (3 / 4 : ℝ) * (20 * R ^ 3) := by ring
      _ ≤ Y ^ (3 / 4 : ℝ) * Y ^ (1 / 20 : ℝ) := mul_le_mul_of_nonneg_left t1 (by linarith)
      _ = Y ^ (4 / 5 : ℝ) := s1.symm
  · rw [s2]
    have : Y ^ (4 / 5 : ℝ) * 3 ≤ Y ^ (4 / 5 : ℝ) * Y ^ (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left t2 (by linarith)
    linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
