-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:07:53.7368+00:00
-- url     : https://prove2.me/submissions/1bba8db2-d4d3-4693-812d-fd40824f6ccf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section
/-- Lower bound of physical discounted Stieltjes cash from endpoint weight. -/
theorem solution
    (μ : Measure ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) ≤
      ∫⁻ t in Ioc a b,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by
  calc
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) =
        ∫⁻ t in Ioc a b,
          ENNReal.ofReal (Real.exp (-(q * b))) ∂μ := by
      simp [lintegral_const]
    _ ≤ ∫⁻ t in Ioc a b,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hq (sub_nonneg.mpr ht.2)]
