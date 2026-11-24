-- Prove2me | solution 1 for DeletedPrimes.window_root_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:23.437239+00:00
-- url     : https://prove2.me/submissions/71d93168-91d1-4b4d-be1b-e04555030aa2

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ8 : θ < 1 / 8) :
    (1 - Real.sqrt (1 - 8 * θ)) / 2 * (1 - (1 - Real.sqrt (1 - 8 * θ)) / 2) = 2 * θ ∧
      0 ≤ (1 - Real.sqrt (1 - 8 * θ)) / 2 ∧ (1 - Real.sqrt (1 - 8 * θ)) / 2 < 1 / 2 := by
  have h8 : 0 < 1 - 8 * θ := by linarith
  have hs : Real.sqrt (1 - 8 * θ) ^ 2 = 1 - 8 * θ := Real.sq_sqrt h8.le
  have hs_pos : 0 < Real.sqrt (1 - 8 * θ) := Real.sqrt_pos.2 h8
  have hs_le : Real.sqrt (1 - 8 * θ) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 / 4 : ℝ) * hs
  · linarith
  · linarith
end DeletedPrimes
