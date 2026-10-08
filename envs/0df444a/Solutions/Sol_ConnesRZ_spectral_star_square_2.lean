-- Prove2me | solution 2 for ConnesRZ.spectral_star_square
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T15:07:39.939314+00:00
-- url     : https://prove2.me/submissions/919620be-ee9e-4adc-b91e-e6bc8ebf9189

import Theorems.Thm_ConnesRZ_spectral_weil_pair_hasSum
open Complex MeasureTheory ConnesRZ
theorem solution (g : ℝ → ℂ) (hg : IsTest g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
        (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1))))
      (weilDistribution (conv g (starInv g))) :=
  spectral_weil_pair_hasSum g g (hg.1.of_le (by decide)) hg.1.continuous hg.2 hg.2
