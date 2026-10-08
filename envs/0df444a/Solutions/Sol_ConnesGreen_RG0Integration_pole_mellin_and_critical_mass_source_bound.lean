-- Prove2me | solution 1 for ConnesGreen.RG0Integration.pole_mellin_and_critical_mass_source_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:39:17.078047+00:00
-- url     : https://prove2.me/submissions/6d47e353-3c6c-4b53-bfff-00a43a2a936a

import Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_dirichlet_bound
import Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section


theorem solution (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖mellinHat g 0‖ ^ 2 + ‖mellinHat g 1‖ ^ 2 +
      (∫ r : ℝ, ‖mellinHat g (1/2 + I*r)‖ ^ 2) ≤
      (16 * t ^ 2 * Real.exp t + 8 * Real.pi) *
        ‖sourceEmbed t (problemOneL g)‖ ^ 2 := by
  have he := actual_physical_test_norm t ht g hg
  have h0 := supported_mellin_norm_sq_dirichlet_bound t ht.le g hg 0
  have h1 := supported_mellin_norm_sq_dirichlet_bound t ht.le g hg 1
  norm_num at h0 h1
  have hx : 2 * |(0 : ℝ) - 1 / 2| * t = t := by norm_num
  have hy : 2 * |(1 : ℝ) - 1 / 2| * t = t := by norm_num
  have hm := critical_mellin_mass_identity g hg.1
  have hd : 0 ≤ ∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hp := Real.pi_pos
  have hh : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 4 * ‖sourceEmbed t (problemOneL g)‖ ^ 2 := by rw [he]; nlinarith
  have hmass := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*Real.pi)
  rw [hm]
  rw [he]
  simp only [iteratedDeriv_one] at he hd ⊢
  rw [he] at hmass
  nlinarith
