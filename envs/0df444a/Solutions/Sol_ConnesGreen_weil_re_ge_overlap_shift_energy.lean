-- Prove2me | solution 1 for ConnesGreen.weil_re_ge_overlap_shift_energy
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T03:51:40.256095+00:00
-- url     : https://prove2.me/submissions/6a251b45-ebd8-43e8-b193-248a679a25a0

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
import Theorems.Thm_ConnesGreen_prime_convolution_overlap_mass_bound
import Theorems.Thm_ConnesGreen_pole_pair_re_ge_sinh_mass
import Theorems.Thm_ConnesGreen_arch_convolution_re_ge_frequency_mass
import Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_dirichlet_bound
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
namespace ConnesGreen
theorem arch_convolution_re_ge_neg_energy (R : ℝ) (hR : 0 ≤ R) (g : ℝ → ℂ) (hg : SupportedTest R g) :
    -(4 * max (-Zeta23.EF.gammaBracket 0) 0) * physicalTestEnergy g ≤
      (archTerm (conv g (starInv g))).re := by
  have hm : Zeta23.EF.gammaBracket 0 * (∫ s : ℝ, ‖g s‖ ^ 2) ≤ (archTerm (conv g (starInv g))).re := by
    have h := arch_convolution_re_ge_frequency_mass 0 R (by norm_num) hR g hg
    simpa [Zeta23.EF.gammaBracket] using h
  have hL : 0 ≤ ∫ s : ℝ, ‖g s‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hd : 0 ≤ ∫ s : ℝ, ‖iteratedDeriv 1 g s‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have he : (∫ s : ℝ, ‖g s‖ ^ 2) ≤ 4 * physicalTestEnergy g := by
    unfold physicalTestEnergy
    nlinarith
  have hD : 0 ≤ max (-Zeta23.EF.gammaBracket 0) 0 := le_max_right _ _
  have hγ : -max (-Zeta23.EF.gammaBracket 0) 0 ≤ Zeta23.EF.gammaBracket 0 := by
    linarith [le_max_left (-Zeta23.EF.gammaBracket 0) 0]
  have h1 := mul_le_mul_of_nonneg_right hγ hL
  have h2 := mul_le_mul_of_nonneg_left he hD
  nlinarith
theorem pole_pair_energy_bound (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1‖ ≤
      16 * T ^ 2 * Real.exp T * physicalTestEnergy g := by
  have h0 := supported_mellin_norm_sq_dirichlet_bound T hT g hg 0
  have h1 := supported_mellin_norm_sq_dirichlet_bound T hT g hg 1
  change ‖mellinHat g 0‖ ^ 2 ≤ _ at h0
  change ‖mellinHat g 1‖ ^ 2 ≤ _ at h1
  norm_num at h0 h1
  simp only [← iteratedDeriv_one] at h0 h1
  change ‖mellinHat g 0‖ ^ 2 ≤ 8*T^2*Real.exp T*physicalTestEnergy g at h0
  change ‖mellinHat g 1‖ ^ 2 ≤ 8*T^2*Real.exp T*physicalTestEnergy g at h1
  have hn : ‖mellinHat g 0‖ * ‖mellinHat g 1‖ ≤
      8 * T ^ 2 * Real.exp T * physicalTestEnergy g := by
    nlinarith [sq_nonneg (‖mellinHat g 0‖ - ‖mellinHat g 1‖)]
  have hp := (norm_add_le (mellinHat (conv g (starInv g)) 0)
    (mellinHat (conv g (starInv g)) 1))
  rw [ConnesRZ.mellinHat_conv_starInv g hg.1,
    ConnesRZ.mellinHat_conv_starInv g hg.1] at hp
  simp only [map_zero, map_one, sub_zero, sub_self, norm_mul, RCLike.norm_conj] at hp
  rw [ConnesRZ.mellinHat_conv_starInv g hg.1,
    ConnesRZ.mellinHat_conv_starInv g hg.1]
  simp only [map_zero, map_one, sub_zero, sub_self]
  nlinarith
theorem primeOverlapLoss_le_energy_cost (R : ℝ) (g : ℝ → ℂ) :
    primeOverlapLoss R g ≤ primeOverlapEnergyCost R * physicalTestEnergy g := by
  unfold primeOverlapLoss primeOverlapEnergyCost
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have h := mul_le_mul_of_nonneg_left (min_le_right (∫ s : ℝ, ‖g s‖ ^ 2)
    (2*physicalTestEnergy g*max (2*R-Real.log n) 0))
      (by positivity : 0 ≤ 2*(ArithmeticFunction.vonMangoldt n / Real.sqrt n))
  nlinarith
theorem pole_pair_re_ge_energy_cost (R : ℝ) (hR : 0 ≤ R)
    (g : ℝ → ℂ) (hg : SupportedTest R g) :
    -min (16*R^2*Real.exp R) (8*(Real.sinh R-R))*physicalTestEnergy g ≤
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re := by
  have ha := pole_pair_energy_bound R hR g hg
  have hr := Complex.abs_re_le_norm
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1)
  have hl := neg_abs_le
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re
  have hb := pole_pair_re_ge_sinh_mass R hR g hg
  have hs : 0 ≤ Real.sinh R-R := sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hR)
  have hM : (∫ s : ℝ, ‖g s‖ ^ 2) ≤ 4*physicalTestEnergy g := by
    unfold physicalTestEnergy
    have hd : 0 ≤ ∫ s : ℝ, ‖iteratedDeriv 1 g s‖ ^ 2 := integral_nonneg (fun s => sq_nonneg _)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 2*(Real.sinh R-R))
  rcases le_total (16*R^2*Real.exp R) (8*(Real.sinh R-R)) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; nlinarith
end ConnesGreen
theorem solution (R : ℝ) (hR : 0 ≤ R)
    (g : ℝ → ℂ) (hg : SupportedTest R g) :
    -arithmeticOverlapShift R * physicalTestEnergy g ≤
      (weilDistribution (conv g (starInv g))).re := by
  have ha := arch_convolution_re_ge_neg_energy R hR g hg
  have hp := pole_pair_re_ge_energy_cost R hR g hg
  have hn := (prime_convolution_overlap_mass_bound R g hg).trans
    (primeOverlapLoss_le_energy_cost R g)
  have hr := Complex.abs_re_le_norm (primeSum (conv g (starInv g)))
  have hl := le_abs_self (primeSum (conv g (starInv g))).re
  simp only [Complex.add_re] at hp
  unfold arithmeticOverlapShift weilDistribution
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith
