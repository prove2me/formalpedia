-- Prove2me | solution 1 for Eden.globalGrowthInterpolation_four_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:21.852797+00:00
-- url     : https://prove2.me/submissions/83e80035-daad-46bb-bad6-a55d51699dec

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
import Theorems.Thm_Eden_globalGrowthInterpolation_interpolate
import Theorems.Thm_Eden_globalGrowthRate_five
import Theorems.Thm_Eden_globalGrowthRate_four


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c d : ℝ} (hc : 4 ≤ c)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5) :
    globalGrowthInterpolation c d = 4 - c * (d - 4) := by
  have h := globalGrowthInterpolation_interpolate hc (k := 4) (by norm_num)
    (α := d - 4) (by linarith) (by linarith)
  norm_num only [Nat.cast_ofNat] at h
  rw [show 4 + (d - 4) = d by ring, globalGrowthRate_four hc, globalGrowthRate_five hc] at h
  rw [h]
  ring
end Eden
