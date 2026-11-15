-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a256_scalar_gaussian_HJB_positive_origin_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:27:00.136245+00:00
-- url     : https://prove2.me/submissions/7177fbe6-2ba6-4bc1-a291-40de468c0619

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a247_Gaussian_HJB_scalar_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_ga_a248_Gaussian_HJB_characteristic_roots_signs_sum_product
import Theorems.Thm_AvramDividend_Classical_avram_ga_a250_Gaussian_HJB_factor_antitone_on_positive_reserve_interval
import Theorems.Thm_AvramDividend_Classical_avram_ga_a255_HJB_weighted_factor_positive_origin_uniform_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (sigma c q a : ℝ) (hσ : 0 < sigma) (hq : 0 < q) (ha : 0 < a)
    (w : ℝ → ℝ)
    (hSmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hODE : ∀ y : ℝ, 0 < y →
      sigma^2/2 * iteratedDeriv 2 w y +
        c * deriv w y - q * w y ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y ≤ a → w y ≤ K := by
  let root : ℝ := Real.sqrt (c^2+2*q*sigma^2)
  let lp : ℝ := (-c+root)/sigma^2
  let lm : ℝ := (-c-root)/sigma^2
  have hr := avram_ga_a248_Gaussian_HJB_characteristic_roots_signs_sum_product
    sigma c q hσ hq
  change 0 < lp ∧ lm < 0 ∧
    lp+lm = -2*c/sigma^2 ∧ lp*lm = -2*q/sigma^2 at hr
  obtain ⟨hlp,hlm,hsum,hprod⟩ := hr
  have hCont : ContinuousOn w (Set.Ioi 0) := by
    intro t ht
    exact ((hSmooth t ht).1).continuousAt.continuousWithinAt
  have hfpCont : ContinuousOn (deriv w) (Set.Ioi 0) := by
    intro t ht
    exact ((hSmooth t ht).2).continuousAt.continuousWithinAt
  have hgCont : ContinuousOn (fun t => Real.exp (-lm*t)*
      (deriv w t-lp*w t)) (Set.Ioi 0) := by
    have hexp : Continuous (fun t : ℝ => Real.exp (-lm*t)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact hexp.continuousOn.mul
      (hfpCont.sub (continuousOn_const.mul hCont))
  have hFac (t : ℝ) (ht : t ∈ Set.Ioo 0 a) :
      iteratedDeriv 2 w t-(lp+lm)*deriv w t+lp*lm*w t ≤ 0 := by
    have heq := avram_ga_a247_Gaussian_HJB_scalar_factorisation
      sigma c q lp lm (deriv w t)
      (iteratedDeriv 2 w t) (w t) hsum hprod hσ
    have hm : sigma^2/2 *
      (iteratedDeriv 2 w t-(lp+lm)*deriv w t+lp*lm*w t) ≤ 0 := by
      rw [heq]
      exact hODE t ht.1
    have hpos : 0 < sigma^2/2 := by positivity
    by_contra h
    have hp : 0 < iteratedDeriv 2 w t-
        (lp+lm)*deriv w t+lp*lm*w t := lt_of_not_ge h
    have hc := mul_pos hpos hp
    linarith
  have hFactor (t : ℝ) (ht : t ∈ Set.Ioo 0 a) :
      Real.exp (-lm*a)*(deriv w a-lp*w a) ≤
      Real.exp (-lm*t)*(deriv w t-lp*w t) := by
    have hsub : Set.Icc t a ⊆ Set.Ioi (0:ℝ) := by
      intro u hu
      exact lt_of_lt_of_le ht.1 hu.1
    exact avram_ga_a250_Gaussian_HJB_factor_antitone_on_positive_reserve_interval
      w (deriv w) (fun z => iteratedDeriv 2 w z)
      lp lm a t ht.1 ht.2.le
      (fun z hz => (hSmooth z hz.1).1)
      (fun z hz => (hSmooth z hz.1).2)
      (hgCont.mono hsub) hFac
  exact avram_ga_a255_HJB_weighted_factor_positive_origin_uniform_upper
    w (deriv w) a lp lm ha hlp.le (by linarith)
    hCont (fun z hz => (hSmooth z hz.1).1) hFactor
