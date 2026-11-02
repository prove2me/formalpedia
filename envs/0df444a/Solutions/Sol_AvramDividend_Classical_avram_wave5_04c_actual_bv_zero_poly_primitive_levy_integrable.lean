-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:38:21.420676+00:00
-- url     : https://prove2.me/submissions/19f17cec-3ce0-40fe-b749-0be19a91778b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! Every exact zero-constant polynomial negative-jump primitive is
Bochner integrable under the genuine BV Lévy measure. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) :
    IntegrableOn (fun y : ℝ =>
      ∫ r in (0 : ℝ)..(-y),
        Polynomial.eval (Real.exp (-r)) p)
      (Iio (0 : ℝ)) X.ν := by
  have hIntegrable (k : ℕ) (hk : k ∈ p.support.erase 0) :
      IntegrableOn (fun y : ℝ => 1 - Real.exp ((k : ℝ) * y))
        (Iio (0 : ℝ)) X.ν := by
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    have hh := bv_exponential_jump_integrable X hBV (k : ℝ) hk1
    have hEq : (fun y : ℝ => 1 - Real.exp ((k : ℝ) * y)) =
        (fun y : ℝ => -(Real.exp ((k : ℝ) * y) - 1)) := by
      funext y
      ring
    rw [hEq]
    exact hh.neg
  have hIntSum :
      IntegrableOn
        (fun y : ℝ => ∑ k ∈ p.support.erase 0,
          (p.coeff k / (k : ℝ)) * (1 - Real.exp ((k : ℝ) * y)))
        (Iio (0 : ℝ)) X.ν := by
    apply integrable_finset_sum
    intro k hk
    exact (hIntegrable k hk).const_mul _
  have hEq (y : ℝ) :
      (∫ r in (0 : ℝ)..(-y),
        Polynomial.eval (Real.exp (-r)) p) =
      ∑ k ∈ p.support.erase 0,
        (p.coeff k / (k : ℝ)) *
          (1 - Real.exp ((k : ℝ) * y)) := by
    rw [avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits p hp (-y)]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mul_neg, neg_neg]
    ring
  convert hIntSum using 1
  ext y
  exact hEq y
