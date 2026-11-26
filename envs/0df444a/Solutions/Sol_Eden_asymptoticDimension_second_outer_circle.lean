-- Prove2me | solution 1 for Eden.asymptoticDimension_second_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:58.456431+00:00
-- url     : https://prove2.me/submissions/b47d80ff-ae44-470d-b69b-4762ef0400ed

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 2) : asymptoticDimension c p = 1 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  rw [descending_radiusPairSpectrum_zero_two hc, kaplanYorkeDimension_zero_two hc]
end Eden
