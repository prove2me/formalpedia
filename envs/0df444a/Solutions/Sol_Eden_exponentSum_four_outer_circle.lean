-- Prove2me | solution 1 for Eden.exponentSum_four_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:53.777279+00:00
-- url     : https://prove2.me/submissions/5713eef5-2deb-4560-b127-9db483036413

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    spectrumPartialSum (lyapunovExponent c p) 4 = -8 := by
  have hs : lyapunovExponent c p = ![0, -2, -2, -4, -c] := by
    rcases hp with hp | hp
    · rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
      norm_num [limitingSquaredRadius]
      rw [descending_radiusPairSpectrum_swap c 2 0, descending_radiusPairSpectrum_zero_two hc]
    · rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
      norm_num [limitingSquaredRadius]
      exact descending_radiusPairSpectrum_zero_two hc
  rw [hs]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
end Eden
