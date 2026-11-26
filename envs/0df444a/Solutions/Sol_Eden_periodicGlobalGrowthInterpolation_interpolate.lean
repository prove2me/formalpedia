-- Prove2me | solution 1 for Eden.periodicGlobalGrowthInterpolation_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:08.033811+00:00
-- url     : https://prove2.me/submissions/4bd9959e-6859-420f-a162-95a8d342533f

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_eq
import Theorems.Thm_Eden_periodicGlobalGrowthRate_eq
import Theorems.Thm_Eden_spectrumInterpolation_interpolate
import Theorems.Thm_Eden_spectrumPartialSum_succ


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k < 5) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
      (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1) := by
  rw [periodicGlobalGrowthInterpolation_eq hc,
    spectrumInterpolation_interpolate _ hk hα₀ hα₁,
    periodicGlobalGrowthRate_eq hc (by omega), periodicGlobalGrowthRate_eq hc (by omega),
    spectrumPartialSum_succ]
  ring
end Eden
