-- Prove2me | solution 1 for ConnesGreen.pole_pair_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:46:53.222261+00:00
-- url     : https://prove2.me/submissions/9cd9e35e-a650-40ea-971e-0f0a1c70b72c

import Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_mass_bound
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
theorem solution (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1‖ ≤
      4 * T * Real.exp T * (∫ s : ℝ, ‖g s‖ ^ 2) := by
  have h0 := supported_mellin_norm_sq_mass_bound T hT g hg 0
  have h1 := supported_mellin_norm_sq_mass_bound T hT g hg 1
  norm_num at h0 h1
  have hn : ‖mellinHat g 0‖ * ‖mellinHat g 1‖ ≤
      2 * T * Real.exp T * (∫ s : ℝ, ‖g s‖ ^ 2) := by
    nlinarith [sq_nonneg (‖mellinHat g 0‖ - ‖mellinHat g 1‖)]
  have hp := norm_add_le (mellinHat (conv g (starInv g)) 0)
    (mellinHat (conv g (starInv g)) 1)
  rw [ConnesRZ.mellinHat_conv_starInv g hg.1,
    ConnesRZ.mellinHat_conv_starInv g hg.1] at hp
  simp only [map_zero, map_one, sub_zero, sub_self, norm_mul, RCLike.norm_conj] at hp
  rw [ConnesRZ.mellinHat_conv_starInv g hg.1,
    ConnesRZ.mellinHat_conv_starInv g hg.1]
  simp only [map_zero, map_one, sub_zero, sub_self]
  nlinarith

