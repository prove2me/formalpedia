-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_cash_mesh_le_unfiltered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:30:53.897221+00:00
-- url     : https://prove2.me/submissions/6391c0f9-0ecb-4939-8012-0028f7941840

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Removing the strict horizon restriction can only increase
nonnegative original dividend cash on the physical stopped cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m n : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (∑ i ∈ Finset.range n,
      ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩
        Iio (T : ℝ)) ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
        f t ∂(dividendMeasure D ω)) ≤
    (∑ i ∈ Finset.range n,
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
        f t ∂(dividendMeasure D ω)) := by
  apply Finset.sum_le_sum
  intro i hi
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  exact ⟨ht.1.1, ht.2⟩
