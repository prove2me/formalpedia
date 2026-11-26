-- Prove2me | solution 1 for Eden.normalizedLogSingularValues_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:06.479587+00:00
-- url     : https://prove2.me/submissions/c6ce1a38-cf83-4a3a-938c-135b27b13b03

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_normalizedLogSingularValues_of_stationary_radii
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] := by
  rcases hp with hp | hp
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inr (Or.inr hp.1)) (Or.inl hp.2.1), hp.1, hp.2.1,
      descending_radiusPairSpectrum_swap c 2 0, descending_radiusPairSpectrum_zero_two hc]
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inl hp.1) (Or.inr (Or.inr hp.2.1)), hp.1, hp.2.1,
      descending_radiusPairSpectrum_zero_two hc]
end Eden
