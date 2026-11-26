-- Prove2me | solution 1 for Eden.dist_projection_evolution_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:12.639022+00:00
-- url     : https://prove2.me/submissions/d43fcba3-7e8a-42b4-8134-b94d0cb7a0bc

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_radial_excess_le
import Theorems.Thm_Eden_dist_attractorProjection_sq
import Theorems.Thm_Eden_radiusEvolution_ge_sqrt_two
import Theorems.Thm_P2M_Eden_radius__evolution_5f79e8068ad6
import Theorems.Thm_P2M_Eden_radius__evolution_affebfa495cb


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W) :
    dist (evolution c t p) (attractorProjection (evolution c t p)) ^ 2 ≤
      attractionBound c M W t := by
  rw [dist_attractorProjection_sq, radius₁_evolution c ht, radius₂_evolution c ht]
  have hb₁ := radial_excess_le ht (Real.sqrt_nonneg _) h₁ hM
  have hb₂ := radial_excess_le ht (Real.sqrt_nonneg _) h₂ hM
  have hb₀ : 0 ≤ radiusEvolution t M - Real.sqrt 2 := by
    linarith [radiusEvolution_ge_sqrt_two ht hM]
  have he : (Real.exp (-c * t)) ^ 2 = Real.exp (-2 * c * t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hw₂ : p 4 ^ 2 ≤ W ^ 2 := by nlinarith [sq_abs (p 4), abs_nonneg (p 4)]
  have hwbound := mul_le_mul_of_nonneg_left hw₂ (Real.exp_pos (-2 * c * t)).le
  have hwformula : evolution c t p 4 ^ 2 = Real.exp (-2 * c * t) * p 4 ^ 2 := by
    change (Real.exp (-c * t) * p 4) ^ 2 = _
    rw [mul_pow, he]
  rw [hwformula]
  unfold attractionBound
  nlinarith [le_max_right (radiusEvolution t (Real.sqrt (radiusSq₁ p)) - Real.sqrt 2) 0,
    le_max_right (radiusEvolution t (Real.sqrt (radiusSq₂ p)) - Real.sqrt 2) 0]
end Eden
