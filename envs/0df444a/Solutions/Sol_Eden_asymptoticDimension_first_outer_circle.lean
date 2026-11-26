-- Prove2me | solution 1 for Eden.asymptoticDimension_first_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:19.938798+00:00
-- url     : https://prove2.me/submissions/d388cfe4-4103-42b6-8171-42dd02dc8ee7

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2) : asymptoticDimension c p = 1 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_swap c 2 0, descending_radiusPairSpectrum_zero_two hc,
    kaplanYorkeDimension_zero_two hc]
end Eden
