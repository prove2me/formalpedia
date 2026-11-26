-- Prove2me | solution 1 for Eden.periodicGlobalGrowthInterpolation_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:10.872734+00:00
-- url     : https://prove2.me/submissions/5fdce6e0-c8cd-40bc-b4fb-93f9836a3919

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_eq
import Theorems.Thm_Eden_periodicGlobalGrowthRate_eq
import Theorems.Thm_Eden_spectrumInterpolation_integer


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalGrowthInterpolation c k = periodicGlobalGrowthRate c k := by
  rw [periodicGlobalGrowthInterpolation_eq hc, spectrumInterpolation_integer _ hk,
    periodicGlobalGrowthRate_eq hc hk]
end Eden
