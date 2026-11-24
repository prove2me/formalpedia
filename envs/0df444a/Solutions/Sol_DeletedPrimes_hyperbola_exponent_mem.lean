-- Prove2me | solution 1 for DeletedPrimes.hyperbola_exponent_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:09:55.347804+00:00
-- url     : https://prove2.me/submissions/651cd869-9d0b-4278-b121-6394cc2074fc

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {β γ : ℝ} (hγ0 : 0 ≤ γ) (hγβ : γ < β) (hβ1 : β ≤ 1) :
    0 < β / (1 + β - γ) ∧ β / (1 + β - γ) ≤ 1 := by
  have hpos : 0 < 1 + β - γ := by linarith
  refine ⟨div_pos (by linarith) hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  linarith
end DeletedPrimes
