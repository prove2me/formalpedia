-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a252_Gaussian_HJB_supersolution_factor_derivative_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:15:17.534256+00:00
-- url     : https://prove2.me/submissions/5357ef45-513d-4860-992c-0da4f5abd296

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a247_Gaussian_HJB_scalar_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (f fp : ℝ → ℝ)
    (sigma c q lambdaPlus lambdaMinus fpp y : ℝ)
    (hSigma : 0 < sigma)
    (hSum : lambdaPlus + lambdaMinus = -2*c/sigma^2)
    (hProd : lambdaPlus * lambdaMinus = -2*q/sigma^2)
    (hf : HasDerivAt f (fp y) y)
    (hfp : HasDerivAt fp fpp y)
    (hHJB : (sigma^2/2)*fpp+c*fp y-q*f y ≤ 0) :
    deriv (fun t => Real.exp (-lambdaMinus*t)*
      (fp t-lambdaPlus*f t)) y ≤ 0 := by
  have hd := (avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
    f fp fpp lambdaPlus lambdaMinus y hf hfp).deriv
  rw [hd]
  have hFactor := avram_ga_a247_Gaussian_HJB_scalar_factorisation
    sigma c q lambdaPlus lambdaMinus (fp y) fpp (f y)
    hSum hProd hSigma
  have hPos : 0 < sigma^2/2 := by positivity
  have hLe : fpp-(lambdaPlus+lambdaMinus)*fp y+
      lambdaPlus*lambdaMinus*f y ≤ 0 := by
    by_contra hn
    have hp : 0 < fpp-(lambdaPlus+lambdaMinus)*fp y+
        lambdaPlus*lambdaMinus*f y := lt_of_not_ge hn
    have hh := mul_pos hPos hp
    rw [hFactor] at hh
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (Real.exp_nonneg _) hLe
