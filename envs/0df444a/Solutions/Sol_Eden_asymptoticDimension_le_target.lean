-- Prove2me | solution 1 for Eden.asymptoticDimension_le_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:43.512548+00:00
-- url     : https://prove2.me/submissions/bfaa71a3-686d-453c-bbed-15ce3e8d0413

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_kaplanYorkeDimension_radiusPair_bound_and_eq
import Theorems.Thm_Eden_limitingSquaredRadius_cases
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    asymptoticDimension c p ≤ targetDimension c := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum]
  exact (kaplanYorkeDimension_radiusPair_bound_and_eq hc
    (limitingSquaredRadius_cases _) (limitingSquaredRadius_cases _)).1
end Eden
