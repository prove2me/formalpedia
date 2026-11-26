-- Prove2me | solution 1 for Eden.asymptoticDimension_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:53.555073+00:00
-- url     : https://prove2.me/submissions/d51fd5f3-9462-45f4-97a9-09a8fb90ac48

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_zero
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    asymptoticDimension c 0 = 0 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum]
  norm_num [radiusSq₁, radiusSq₂, limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_zero hc, kaplanYorkeDimension_zero_zero hc]
end Eden
