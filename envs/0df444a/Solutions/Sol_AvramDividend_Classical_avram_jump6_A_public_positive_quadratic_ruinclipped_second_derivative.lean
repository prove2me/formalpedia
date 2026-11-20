-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_public_positive_quadratic_ruinclipped_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:09:24.573174+00:00
-- url     : https://prove2.me/submissions/fc53f5cb-8530-4440-9923-0c3b5934f0ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_public_positive_ruinclipped_quadratic_first_derivative
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 < y) :
    iteratedDeriv 2 (fun z : ℝ =>
      if z < 0 then 0 else 1 + z + z ^ 2) y = 2 := by
  let w : ℝ → ℝ :=
    fun z => if z < 0 then 0 else 1 + z + z ^ 2
  change iteratedDeriv 2 w y = 2
  have hE : (deriv w) =ᶠ[𝓝 y] (fun z : ℝ => 1 + 2 * z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact (avram_jump6_A_public_positive_ruinclipped_quadratic_first_derivative
      z hz).1
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  rw [hE.deriv_eq]
  have hder : HasDerivAt (fun z : ℝ => 1 + 2 * z) 2 y := by
    change HasDerivAt
      ((fun _ : ℝ => (1 : ℝ)) + (fun z : ℝ => (2 : ℝ) * z)) 2 y
    convert (hasDerivAt_const y (1 : ℝ)).add
      ((hasDerivAt_id y).const_mul (2 : ℝ)) using 1 <;>
      first | rfl | ring
  exact hder.deriv