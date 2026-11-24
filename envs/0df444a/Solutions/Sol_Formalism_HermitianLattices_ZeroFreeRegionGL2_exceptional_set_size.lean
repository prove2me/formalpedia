-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.exceptional_set_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:50.096504+00:00
-- url     : https://prove2.me/submissions/dc4de6ad-8559-460f-b62e-55c597f7e0b6

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
theorem _root_.solution : TstarSize := by
  intro ε δ A C hε hδ hA hC
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_le_rpow (2 * ε / 3) 8 (by positivity)).and
      ((eventually_affine_log_le_rpow ε 0 A (1 / 8) hε (by norm_num)).and
        ((eventually_le_rpow δ (8 * C) hδ).and ((eventually_le_rpow δ 8 hδ).and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨x₀, fun x hx m k n hn1 hn2 hm hk => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := by linarith
  set L : ℝ := x ^ ε with hL
  set s : ℝ := x ^ (ε / 3) with hs
  have hL1 : 1 ≤ L := Real.one_le_rpow e5 hε.le
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hLs : L = s * x ^ (2 * ε / 3) := by
    rw [hL, hs, ← Real.rpow_add hx0]; congr 1; ring
  have hs8 : 8 * s ≤ L := by
    rw [hLs]
    have := mul_le_mul_of_nonneg_left e1 hs0.le
    linarith
  have hm8C : 8 * C ≤ m := le_trans e3 hm
  have hm8 : 8 ≤ m := le_trans e4 hm
  have hm0 : 0 < m := by linarith
  have hln : Real.log n ≤ A * Real.log x := by
    have := Real.log_le_log hn0 hn2
    rwa [Real.log_rpow hx0] at this
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hq : m ^ 2 * L / k ≤ 1 := by rw [div_le_one hk0]; exact hk
  have hlog : Real.log (x * Real.exp L / Real.exp s / (x * n)) = L - s - Real.log n := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp]
    ring
  have hmL : 8 ≤ m * L := by
    have := mul_le_mul hm8 hL1 zero_le_one hm0.le
    linarith
  constructor
  · rw [hlog]
    have t1 : 3 * L / 4 ≤ L - s - Real.log n := by linarith
    have t2 : m * (3 * L / 4) ≤ m * (L - s - Real.log n) := mul_le_mul_of_nonneg_left t1 hm0.le
    have t3 : C * (L + m ^ 2 * L / k) ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hC.le
    have t4 : 8 * C * L ≤ m * L := mul_le_mul_of_nonneg_right hm8C (by linarith)
    linarith
  · intro Xu Gam fk hXu hGam hfk hlX hlG
    have hG0 : 0 < Gam := by linarith
    rw [Real.log_mul hXu.ne' (Real.rpow_pos_of_pos hG0 _).ne', Real.log_rpow hG0]
    have t1 : Real.log Gam / fk ≤ 1 := by rw [div_le_one hfk]; exact hlG
    have t2 : -2 / fk * Real.log Gam = -2 * (Real.log Gam / fk) := by ring
    rw [t2]
    linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
