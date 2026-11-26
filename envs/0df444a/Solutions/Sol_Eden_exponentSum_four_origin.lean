-- Prove2me | solution 1 for Eden.exponentSum_four_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:28.430164+00:00
-- url     : https://prove2.me/submissions/02e358e9-e265-4655-a93d-6b8659429f97

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    spectrumPartialSum (lyapunovExponent c 0) 4 = -8 := by
  rw [lyapunovExponent_eq_radiusPairSpectrum]
  norm_num [radiusSq₁, radiusSq₂, limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_zero hc]
  norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
end Eden
