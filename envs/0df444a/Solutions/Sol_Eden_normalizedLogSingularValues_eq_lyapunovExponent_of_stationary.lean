-- Prove2me | solution 1 for Eden.normalizedLogSingularValues_eq_lyapunovExponent_of_stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:19.73346+00:00
-- url     : https://prove2.me/submissions/e661f75a-198f-427c-81fb-7ebb40f14b92

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_limitingSquaredRadius_of_stationary
import Theorems.Thm_Eden_normalizedLogSingularValues_of_stationary_radii
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ)
    {t : ℝ} (ht : 0 < t) (p : PhaseSpace)
    (h₁ : radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :
    normalizedLogSingularValues c t p = lyapunovExponent c p := by
  rw [normalizedLogSingularValues_of_stationary_radii c ht p h₁ h₂,
    lyapunovExponent_eq_radiusPairSpectrum, limitingSquaredRadius_of_stationary h₁,
    limitingSquaredRadius_of_stationary h₂]
end Eden
