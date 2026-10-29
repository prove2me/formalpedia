-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_levy_positive_root_strict_gap_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:54:39.403212+00:00
-- url     : https://prove2.me/submissions/165d582d-be4d-48cb-909e-97354918c634

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Convexity and normalisation make every nonnegative parameter
strictly below a positive root lie in the finite moment-rate gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : 0 ≤ β)
    (hβlam : β < lam) :
    X.ψ β < p := by
  let t : ℝ := β / lam
  have ht0 : 0 ≤ t := div_nonneg hβ hlam.le
  have ht1 : t < 1 := (div_lt_one hlam).mpr hβlam
  have hweight : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  have hcomb : (1 - t) * (0 : ℝ) + t * lam = β := by
    dsimp [t]
    field_simp [ne_of_gt hlam] <;> ring
  have hψzero : X.ψ 0 = 0 := levy_laplace_exponent_zero X
  have hconv := (levy_laplace_exponent_convexOn_nonnegative X).2
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show lam ∈ Ici (0 : ℝ) by exact hlam.le)
    hweight ht0 hsum
  simp only [smul_eq_mul] at hconv
  have hbound : X.ψ β ≤ t * p := by
    rw [hcomb, hψzero, hroot] at hconv
    simpa using hconv
  have htp : t * p < p := by
    nlinarith [mul_lt_mul_of_pos_right ht1 hp]
  linarith
