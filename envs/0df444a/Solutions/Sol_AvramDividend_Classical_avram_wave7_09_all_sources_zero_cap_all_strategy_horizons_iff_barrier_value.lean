-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_all_sources_zero_cap_all_strategy_horizons_iff_barrier_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:54:16.660043+00:00
-- url     : https://prove2.me/submissions/aba6f5a8-7b5e-49e2-93ca-869db42278a1

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- All original Standing sources: the sharp uniform expected complete
Stieltjes cash allowance over all genuine zero-capped strategies and all
integer horizons is exactly the original zero-barrier dividendValue. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ A) ↔
    dividendValue X q 0 (barrierStrategy X 0 0) ≤ A := by
  constructor
  · intro hAll
    have hBarrier : IsAdmissibleLe X 0 (0 : ℝ≥0∞)
        (barrierStrategy X 0 0) := by
      simpa only [ENNReal.ofReal_zero] using
        (barrierStrategy_admissibleLe_nonnegative_barrier
          X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
    exact dividendValue_le_of_uniform_truncated_bounds
      X q 0 (barrierStrategy X 0 0) hBarrier.1 A
      (hAll (barrierStrategy X 0 0) hBarrier)
  · intro hBudget D hD n
    have hFiniteBound :
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
        dividendValue X q 0 D := by
      rw [dividendValue_eq_iSup_truncated X q 0 D hD.1]
      exact le_iSup_of_le n le_rfl
    exact (hFiniteBound.trans
      (zero_cap_admissible_dividendValue_le_barrier_at_zero
        X hX q hq D hD)).trans hBudget
