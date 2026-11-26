-- Prove2me | solution 1 for Eden.globalGrowthInterpolation_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:05.726458+00:00
-- url     : https://prove2.me/submissions/fee39543-1ed4-41b9-a424-fb1bbeb51d92

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
import Theorems.Thm_Eden_spectrumEntry_globalGrowthIncrements
import Theorems.Thm_Eden_spectrumPartialSum_globalGrowthIncrements
import Theorems.Thm_Eden_spectrumInterpolation_interpolate


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 ≤ c)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    globalGrowthInterpolation c ((k : ℝ) + α) =
      (1 - α) * globalGrowthRate c k + α * globalGrowthRate c (k + 1) := by
  rw [globalGrowthInterpolation, spectrumInterpolation_interpolate _ hk hα₀ hα₁,
    spectrumPartialSum_globalGrowthIncrements hc (by omega),
    spectrumEntry_globalGrowthIncrements c hk]
  ring
end Eden
