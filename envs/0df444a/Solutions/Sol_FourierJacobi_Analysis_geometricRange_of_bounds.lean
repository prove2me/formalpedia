-- Prove2me | solution 1 for FourierJacobi.Analysis.geometricRange_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:42.424401+00:00
-- url     : https://prove2.me/submissions/7eeeaf02-d82e-4d47-9f05-35ae7f434eae

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution {t T : ℝ} {d U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : t ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1) (hstrict : T * t < ‖d‖)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) :
    GeometricRange (t : ℂ) d U V (T : ℂ) := by
  have ht : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht₀]
  have hT : ‖(T : ℂ)‖ = T := by simp [abs_of_nonneg hT₀]
  have hdpos : 0 < ‖d‖ := lt_of_lt_of_le ht₀ hd₀
  have ht2 : t ^ 2 < 1 := pow_lt_one₀ (le_of_lt ht₀) ht₁ (by decide)
  have ht4 : t ^ 4 < 1 := pow_lt_one₀ (le_of_lt ht₀) ht₁ (by decide)
  have hT2 : T ^ 2 ≤ 1 := pow_le_one₀ hT₀ hT₁
  have hprod : ‖d‖ * T ≤ 1 := by nlinarith [norm_nonneg d]
  constructor
  · simpa only [norm_pow, ht] using ht2
  · simp only [norm_mul, ht, hT, hV, mul_one]
    nlinarith
  · simp only [norm_div, norm_mul, ht, hT, hV, mul_one]
    exact (div_lt_one hdpos).mpr hstrict
  · simp only [norm_mul, norm_pow, ht, hT, hV, mul_one]
    nlinarith [sq_nonneg t]
  · simp only [norm_mul, norm_pow, ht, hT, hU, mul_one]
    nlinarith [sq_nonneg t]
  · simp only [norm_mul, norm_pow, ht, hT, hU, mul_one]
    nlinarith [sq_nonneg (t ^ 2)]
end FourierJacobi.Analysis
