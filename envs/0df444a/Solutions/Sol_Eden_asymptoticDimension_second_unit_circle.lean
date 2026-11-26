-- Prove2me | solution 1 for Eden.asymptoticDimension_second_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:15.0325+00:00
-- url     : https://prove2.me/submissions/2d5319e3-624b-41b9-b6c8-2ee2ee247d92

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 1) : asymptoticDimension c p = 3 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_one hc, kaplanYorkeDimension_zero_one hc]
end Eden
