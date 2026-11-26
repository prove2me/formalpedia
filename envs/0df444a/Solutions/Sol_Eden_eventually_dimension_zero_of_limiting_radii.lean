-- Prove2me | solution 1 for Eden.eventually_dimension_zero_of_limiting_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:38.707745+00:00
-- url     : https://prove2.me/submissions/011c56d5-5157-44f1-9771-15d395c379d3

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_eventually_dimension_zero_of_first_exponent_neg
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0) :
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by
  apply eventually_dimension_zero_of_first_exponent_neg c p
  rw [lyapunovExponent_eq_radiusPairSpectrum c p, h₁, h₂,
    descending_radiusPairSpectrum_zero_zero hc]
  norm_num
end Eden
