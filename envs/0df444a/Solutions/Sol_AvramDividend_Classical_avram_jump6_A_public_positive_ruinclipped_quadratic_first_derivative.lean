-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_public_positive_ruinclipped_quadratic_first_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:27:54.517173+00:00
-- url     : https://prove2.me/submissions/383da207-9cd4-48a5-913b-063478a04696

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 < y) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else 1 + z + z ^ 2
    deriv w y = 1 + 2 * y ∧ 1 ≤ deriv w y := by
  dsimp
  have hE : (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2)
      =ᶠ[𝓝 y] (fun z : ℝ => 1 + z + z ^ 2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    have hzpos : (0 : ℝ) < z := hz
    simp only [if_neg (not_lt.mpr (le_of_lt hzpos))]
  have hp : HasDerivAt (fun z : ℝ => 1 + z + z ^ 2)
      (1 + 2 * y) y := by
    change HasDerivAt
      ((fun _ : ℝ => (1 : ℝ)) + (fun z : ℝ => z) + (fun z : ℝ => z ^ 2))
      (1 + 2 * y) y
    convert (((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      (hasDerivAt_pow 2 y)) using 1 <;> first | rfl | ring
  have hDer : deriv (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2) y =
      1 + 2 * y := by
    rw [hE.deriv_eq]
    exact hp.deriv
  exact ⟨hDer, by rw [hDer]; linarith⟩
