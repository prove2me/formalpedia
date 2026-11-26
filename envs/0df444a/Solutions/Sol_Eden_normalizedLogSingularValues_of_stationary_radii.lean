-- Prove2me | solution 1 for Eden.normalizedLogSingularValues_of_stationary_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:06.570173+00:00
-- url     : https://prove2.me/submissions/83d17fcb-e0e0-48be-8044-d3b23a0ba06a

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_log_planarAmplitude_div_of_stationary
import Theorems.Thm_Eden_log_radialAmplitude_div_of_stationary
import Theorems.Thm_Eden_normalizedLogSingularValues_eq_descending


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ}
    (ht : 0 < t) (p : PhaseSpace)
    (h₁ : radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2)
    (h₂ : radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :
    normalizedLogSingularValues c t p =
      descending (radiusPairSpectrum c (radiusSq₁ p) (radiusSq₂ p)) := by
  rw [normalizedLogSingularValues_eq_descending c ht p]
  congr 1
  funext i
  fin_cases i
  · exact log_radialAmplitude_div_of_stationary ht h₁
  · exact log_planarAmplitude_div_of_stationary ht h₁
  · exact log_radialAmplitude_div_of_stationary ht h₂
  · exact log_planarAmplitude_div_of_stationary ht h₂
  · change Real.log (Real.exp (-c * t)) / t = -c
    rw [Real.log_exp]
    field_simp
end Eden
