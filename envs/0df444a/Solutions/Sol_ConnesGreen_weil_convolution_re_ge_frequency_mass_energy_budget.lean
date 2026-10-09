-- Prove2me | solution 1 for ConnesGreen.weil_convolution_re_ge_frequency_mass_energy_budget
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T00:41:26.005621+00:00
-- url     : https://prove2.me/submissions/da72edcf-80a9-46a4-bf72-552728c73965

import Theorems.Thm_ConnesGreen_prime_convolution_mass_bound
import Theorems.Thm_ConnesGreen_pole_pair_mass_bound
import Theorems.Thm_ConnesGreen_arch_convolution_re_ge_frequency_mass
import Theorems.Thm_ConnesGreen_convolution_overlap_dirichlet_energy_bound
import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen
private theorem physicalTestEnergy_nonnegative (g : ℝ → ℂ) :
    0 ≤ physicalTestEnergy g := by
  unfold physicalTestEnergy
  exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _)))
namespace ConnesGreen
theorem convolution_starInv_zero_outside (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (x : ℝ) (hx : 2 * t ≤ |x|) :
    conv g (starInv g) x = 0 := by
  unfold conv starInv
  apply integral_eq_zero_of_ae
  filter_upwards [] with s
  by_cases hs : g s = 0
  · simp [hs]
  by_cases hxg : g (-(x - s)) = 0
  · simpa [neg_sub] using (show g s * starRingEnd ℂ (g (-(x - s))) = 0 by rw [hxg]; simp)
  have hs' := hg.2 (subset_tsupport g hs)
  have hxg' := hg.2 (subset_tsupport g hxg)
  have hlt : |x| < 2 * t := abs_lt.mpr ⟨by linarith [hs'.1, hxg'.2],
    by linarith [hs'.2, hxg'.1]⟩
  exact False.elim ((not_lt_of_ge hx) hlt)

/-- Original prime summands vanish outside the explicit active prime-power cutoff. -/
theorem prime_summand_zero_outside_active (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (n : ℕ) (hn : n ∉ activePrimePowerFinset t) :
    ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n = 0 := by
  by_cases hpp : IsPrimePow n
  · have hlog : 2 * t ≤ Real.log (n : ℝ) := by
      have := mt (mem_activePrimePowerFinset t n).mpr hn
      exact le_of_not_gt (fun h => this ⟨hpp, h⟩)
    have hp := convolution_starInv_zero_outside t g hg (Real.log n)
      (hlog.trans (le_abs_self _))
    have hm := convolution_starInv_zero_outside t g hg (-Real.log n)
      (by simpa only [abs_neg] using hlog.trans (le_abs_self (Real.log (n : ℝ))))
    simp [ConnesRZArithmetic.explicitPrimeSummand, hp, hm]
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    simp [ConnesRZArithmetic.explicitPrimeSummand, hz]

/-- A convergent finite family, not a totalized tsum value. -/
theorem prime_convolution_summable (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) :
    Summable (ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g))) := by
  apply summable_of_hasFiniteSupport
  apply (activePrimePowerFinset t).finite_toSet.subset
  intro n hn
  by_contra h
  exact hn (prime_summand_zero_outside_active t g hg n h)

/-- Exact original prime contribution, with no unspecified truncation index. -/
theorem prime_convolution_eq_active_sum (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) :
    primeSum (conv g (starInv g)) = ∑ n ∈ activePrimePowerFinset t,
      ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n := by
  exact tsum_eq_sum (prime_summand_zero_outside_active t g hg)

theorem active_prime_sum_energy_bound (c T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖∑ n ∈ activePrimePowerFinset c,
      ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n‖ ≤
      8 * T * activePrimeWeight c * physicalTestEnergy g := by
  have hb : ∀ x : ℝ, ‖conv g (starInv g) x‖ ≤ 4 * T * physicalTestEnergy g := by
    intro x
    have hm : max (2 * T - |x|) 0 ≤ 2 * T := max_le (by linarith [abs_nonneg x]) (by positivity)
    have h := (convolution_overlap_dirichlet_energy_bound T g hg x).trans
      (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (physicalTestEnergy_nonnegative g)))
    dsimp [physicalTestEnergy] at *
    nlinarith
  have hs : ∀ n : ℕ, ‖ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n‖ ≤
      8 * T * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * physicalTestEnergy g := by
    intro n
    have hw : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := by positivity
    unfold ConnesRZArithmetic.explicitPrimeSummand
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    have h := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (hb (Real.log n)) (hb (-Real.log n)))) hw
    nlinarith
  calc
    _ ≤ ∑ n ∈ activePrimePowerFinset c,
        ‖ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ activePrimePowerFinset c,
        8 * T * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * physicalTestEnergy g :=
      Finset.sum_le_sum (fun n _ => hs n)
    _ = _ := by simp only [activePrimeWeight, Finset.sum_mul, Finset.mul_sum]

theorem prime_convolution_energy_bound (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖primeSum (conv g (starInv g))‖ ≤ 8 * T * activePrimeWeight T * physicalTestEnergy g := by
  rw [prime_convolution_eq_active_sum T g hg]
  exact active_prime_sum_energy_bound T T hT g hg

theorem prime_convolution_mass_energy_min_bound (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    ‖primeSum (conv g (starInv g))‖ ≤
      min (2 * activePrimeWeight T * (∫ s : ℝ, ‖g s‖ ^ 2))
        (8 * T * activePrimeWeight T * physicalTestEnergy g) := by
  exact le_min (prime_convolution_mass_bound T g hg)
    (prime_convolution_energy_bound T hT g hg)

end ConnesGreen
theorem solution
    (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (Zeta23.EF.gammaBracket B -
      (Zeta23.EF.gammaBracket B - Zeta23.EF.gammaBracket 0) *
        (2 * B * T / Real.pi) - 4 * T * Real.exp T) * (∫ s : ℝ, ‖g s‖ ^ 2) -
      min (2 * activePrimeWeight T * (∫ s : ℝ, ‖g s‖ ^ 2))
        (8 * T * activePrimeWeight T * physicalTestEnergy g) ≤
          (weilDistribution (conv g (starInv g))).re := by
  have ha := arch_convolution_re_ge_frequency_mass B T hB hT g hg
  have hp := pole_pair_mass_bound T hT g hg
  have hn := prime_convolution_mass_energy_min_bound T hT g hg
  have hrp := Complex.abs_re_le_norm
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1)
  have hnp := neg_abs_le
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re
  have hrn := Complex.abs_re_le_norm (primeSum (conv g (starInv g)))
  have hnn := le_abs_self (primeSum (conv g (starInv g))).re
  have he : (weilDistribution (conv g (starInv g))).re =
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re -
        (primeSum (conv g (starInv g))).re + (archTerm (conv g (starInv g))).re := by
    simp only [weilDistribution, Complex.add_re, Complex.sub_re]
  rw [he]
  simp only [Zeta23.EF.gammaBracket, Complex.ofReal_zero, mul_zero, zero_div, add_zero] at *
  nlinarith
