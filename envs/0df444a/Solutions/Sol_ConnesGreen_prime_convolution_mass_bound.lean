-- Prove2me | solution 1 for ConnesGreen.prime_convolution_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T00:42:00.445927+00:00
-- url     : https://prove2.me/submissions/ecd915e7-99f2-4c02-9393-d63048639a88

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen
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

theorem convolution_starInv_norm_le_mass (g : ℝ → ℂ) (hg : IsTest g) (x : ℝ) :
    ‖conv g (starInv g) x‖ ≤ ∫ s : ℝ, ‖g s‖ ^ 2 := by
  have hi : Integrable (fun s => ‖g s‖ ^ 2) :=
    (hg.1.continuous.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply] using
        hg.2.norm.mul_right (f' := fun s => ‖g s‖))
  have hj := hi.comp_sub_right x
  have hb (s : ℝ) : ‖g s * starRingEnd ℂ (g (s - x))‖ ≤
      (‖g s‖ ^ 2 + ‖g (s - x)‖ ^ 2) / 2 := by
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖g s‖ - ‖g (s - x)‖)]
  have hm := integral_mono_of_nonneg
    (ae_of_all _ (fun s => norm_nonneg (g s * starRingEnd ℂ (g (s - x)))))
    ((hi.add hj).div_const 2) (ae_of_all _ hb)
  have he : (∫ s : ℝ, (‖g s‖ ^ 2 + ‖g (s - x)‖ ^ 2) / 2) =
      ∫ s : ℝ, ‖g s‖ ^ 2 := by
    rw [integral_div, integral_add hi hj,
      integral_sub_right_eq_self (fun s : ℝ => ‖g s‖ ^ 2) x]
    ring
  unfold conv starInv
  simp only [neg_sub]
  exact (norm_integral_le_integral_norm _).trans (hm.trans_eq he)

end ConnesGreen
theorem solution (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖primeSum (conv g (starInv g))‖ ≤
      2 * activePrimeWeight T * (∫ s : ℝ, ‖g s‖ ^ 2) := by
  have hb (n : ℕ) :
      ‖ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n‖ ≤
        2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (∫ s : ℝ, ‖g s‖ ^ 2) := by
    have hw : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := by positivity
    have hp := convolution_starInv_norm_le_mass g hg.1 (Real.log n)
    have hm := convolution_starInv_norm_le_mass g hg.1 (-Real.log n)
    unfold ConnesRZArithmetic.explicitPrimeSummand
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    have h := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add hp hm)) hw
    nlinarith
  rw [prime_convolution_eq_active_sum T g hg]
  calc
    _ ≤ ∑ n ∈ activePrimePowerFinset T,
        ‖ConnesRZArithmetic.explicitPrimeSummand (conv g (starInv g)) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ activePrimePowerFinset T,
        2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (∫ s : ℝ, ‖g s‖ ^ 2) := Finset.sum_le_sum (fun n _ => hb n)
    _ = _ := by simp only [activePrimeWeight, Finset.sum_mul, Finset.mul_sum]
