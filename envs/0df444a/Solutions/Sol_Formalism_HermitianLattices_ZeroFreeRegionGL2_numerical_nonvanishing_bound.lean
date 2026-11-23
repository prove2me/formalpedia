-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_nonvanishing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:55.170607+00:00
-- url     : https://prove2.me/submissions/d8b7fc20-4b2d-4565-8008-c1c25aa2b3d7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterEstimateOfHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds
  intro ε hε
  have hε' : ε ≠ 0 := ne_of_gt hε
  refine ⟨max 2 ((4:ℝ) ^ (3 / ε)), ?_⟩
  intro x hx y lam hy hlam hlamle
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hx4 : (4:ℝ) ^ (3 / ε) ≤ x := le_trans (le_max_right _ _) hx
  have ht4 : 4 ≤ x ^ (ε / 3) := by
    have h1 : ((4:ℝ) ^ (3 / ε)) ^ (ε / 3) ≤ x ^ (ε / 3) :=
      Real.rpow_le_rpow (by positivity) hx4 (by positivity)
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)] at h1
    have h3 : 3 / ε * (ε / 3) = 1 := by field_simp <;> ring
    rw [h3, Real.rpow_one] at h1
    exact h1
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLne : Real.log x ≠ 0 := ne_of_gt hL
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hly : x ^ (ε / 3) - Real.log 3 ≤ Real.log y := by
    rw [← Real.exp_le_exp, Real.exp_log hypos, Real.exp_sub,
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
    exact hy
  have ha : x ^ (ε / 3) / 2 ≤ Real.log y := by linarith
  refine ⟨ha, ?_, ?_⟩
  · have hsplit : x ^ (ε / 3) = x ^ (2 * ε / 15) * x ^ (ε / 5) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [le_div_iff₀ hlam]
    calc x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) * lam
        ≤ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) * (2 * x ^ (ε / 5) * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hlamle (by positivity)
      _ = x ^ (ε / 3) / 2 := by rw [hsplit]; field_simp <;> ring
      _ ≤ Real.log y := ha
  · have hsplit : x ^ (ε / 3) = x ^ (ε / 6) * x ^ (ε / 6) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hs : 0 ≤ x ^ (ε / 6) / 2 := by positivity
    calc x ^ (ε / 6) / 2 = Real.sqrt ((x ^ (ε / 6) / 2) ^ 2) := (Real.sqrt_sq hs).symm
      _ ≤ Real.sqrt (Real.log y) := by
          apply Real.sqrt_le_sqrt
          have h5 : (x ^ (ε / 6) / 2) ^ 2 = x ^ (ε / 3) / 4 := by rw [hsplit]; ring
          rw [h5]
          have : 0 ≤ x ^ (ε / 3) := by positivity
          linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
