-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:15:29.306764+00:00
-- url     : https://prove2.me/submissions/e8fd5a40-d982-4916-a8e0-f56cf153a431

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
import Theorems.Thm_AvramDividend_Classical_avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Source-faithful discounted cap-barrier physical cash cell lower bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) *
      ENNReal.ofReal (barrierStrategy X c c b.toNNReal ω -
        barrierStrategy X c c a.toNNReal ω) ≤
    (∫⁻ t in Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X c c) ω)) := by
  have hMass :=
    avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
      X c ω a b
  rw [← hMass]
  exact avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
    (dividendMeasure (barrierStrategy X c c) ω) q hq a b
