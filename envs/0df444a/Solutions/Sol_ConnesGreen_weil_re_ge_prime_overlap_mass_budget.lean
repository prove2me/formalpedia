-- Prove2me | solution 1 for ConnesGreen.weil_re_ge_prime_overlap_mass_budget
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T03:01:37.224975+00:00
-- url     : https://prove2.me/submissions/920d98c3-320e-44ad-ba41-30309db39865

import Definitions.Def_ConnesGreen_prime_overlap_loss
import Theorems.Thm_ConnesGreen_prime_convolution_overlap_mass_bound
import Theorems.Thm_ConnesGreen_pole_pair_re_ge_sinh_mass
import Theorems.Thm_ConnesGreen_arch_convolution_re_ge_frequency_mass
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen
theorem solution
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (Zeta23.EF.gammaBracket B -
      (Zeta23.EF.gammaBracket B - Zeta23.EF.gammaBracket 0) *
        (2 * B * T / Real.pi) - 2 * (Real.sinh T - T)) * (∫ s : ℝ, ‖g s‖ ^ 2) -
      primeOverlapLoss T g ≤ (weilDistribution (conv g (starInv g))).re := by
  have ha := arch_convolution_re_ge_frequency_mass B T hB hT g hg
  have hp := pole_pair_re_ge_sinh_mass T hT g hg
  have hn := prime_convolution_overlap_mass_bound T g hg
  have hrn := Complex.abs_re_le_norm (primeSum (conv g (starInv g)))
  have hnn := le_abs_self (primeSum (conv g (starInv g))).re
  have he : (weilDistribution (conv g (starInv g))).re =
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re -
        (primeSum (conv g (starInv g))).re + (archTerm (conv g (starInv g))).re := by
    simp only [weilDistribution, Complex.add_re, Complex.sub_re]
  rw [he]
  simp only [Zeta23.EF.gammaBracket, Complex.ofReal_zero, mul_zero, zero_div, add_zero] at *
  nlinarith
