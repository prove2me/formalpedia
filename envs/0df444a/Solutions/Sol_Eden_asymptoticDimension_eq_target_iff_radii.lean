-- Prove2me | solution 1 for Eden.asymptoticDimension_eq_target_iff_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:44.422294+00:00
-- url     : https://prove2.me/submissions/5a1fb90b-da19-4eb6-a866-fb76106b183a

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_kaplanYorkeDimension_radiusPair_bound_and_eq
import Theorems.Thm_Eden_limitingSquaredRadius_cases
import Theorems.Thm_Eden_limitingSquaredRadius_eq_one_iff
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 := by
  rw [asymptoticDimension, lyapunovExponent_eq_radiusPairSpectrum,
    (kaplanYorkeDimension_radiusPair_bound_and_eq hc
      (limitingSquaredRadius_cases _) (limitingSquaredRadius_cases _)).2,
    limitingSquaredRadius_eq_one_iff, limitingSquaredRadius_eq_one_iff]
end Eden
