-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_cash_grid_discounted_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:22:39.026052+00:00
-- url     : https://prove2.me/submissions/606cc377-8fec-425d-928a-933740b9c0c7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_mesh_le_unfiltered
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (ENNReal.ofReal (rightLimit D 0 ω) +
      ∑ i ∈ Finset.range n,
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩
              Iio (T : ℝ)) ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
  have hmesh :=
    avram_p3_2_original_strict_cash_mesh_le_unfiltered
      X x D ω T m n (fun t => ENNReal.ofReal (Real.exp (-(q * t))))
  have hweight :=
    avram_p3_2_original_finite_stopped_discounted_cash_sum_upper
      X x D ω q hq T m n
  refine le_trans ?_ hweight
  simpa only [add_comm] using
    (add_le_add_left hmesh (ENNReal.ofReal (rightLimit D 0 ω)))
