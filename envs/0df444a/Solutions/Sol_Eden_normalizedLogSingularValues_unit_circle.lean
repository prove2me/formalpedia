-- Prove2me | solution 1 for Eden.normalizedLogSingularValues_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:46.990903+00:00
-- url     : https://prove2.me/submissions/9c3ef970-98d7-4e70-97dd-494e24d32ea3

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_normalizedLogSingularValues_of_stationary_radii
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] := by
  rcases hp with hp | hp
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inr (Or.inl hp.1)) (Or.inl hp.2.1), hp.1, hp.2.1,
      descending_radiusPairSpectrum_swap c 1 0, descending_radiusPairSpectrum_zero_one hc]
  · rw [normalizedLogSingularValues_of_stationary_radii c ht p
      (Or.inl hp.1) (Or.inr (Or.inl hp.2.1)), hp.1, hp.2.1,
      descending_radiusPairSpectrum_zero_one hc]
end Eden
