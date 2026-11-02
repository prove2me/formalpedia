-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:25:38.323028+00:00
-- url     : https://prove2.me/submissions/13a51235-4d41-4969-889d-bce3a710aa9e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine controlled reserve, not a proxy jump kernel, satisfies the
finite-band stopped nonlinear source jump chain balance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (T : Finset ℝ≥0)
    (hT : ∀ q : ℝ≥0, q ∈ T ↔
      s < q ∧ q ≤ t ∧
        X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B) :
    let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
    let J : ℝ≥0 → ℝ := fun q =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y q ∈ Icc (u + δ) v then
        w (riskProcess X x D q ω) -
          w (Function.leftLim
            (fun r : ℝ≥0 => riskProcess X x D r ω) q)
        else 0) else 0) =
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J q then
        J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
        else 0) +
      (if Y q ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
        else 0) else 0) := by
  dsimp only
  classical
  let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
  let J : ℝ≥0 → ℝ := fun q =>
    X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
  have hbase :
      (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y q ∈ Icc (u + δ) v then
          w (Y q + J q) - w (Y q) else 0) else 0) =
      (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if -1 < J q then
          J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
          else 0) +
        (if Y q ∈ Icc (u + δ) v then
          SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
          else 0) else 0) :=
    avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
      X x D hD w u v δ s t ω B hBneg T hT
  have hsum :
      (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y q ∈ Icc (u + δ) v then
          w (riskProcess X x D q ω) -
            w (Function.leftLim
              (fun r : ℝ≥0 => riskProcess X x D r ω) q)
          else 0) else 0) =
      (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y q ∈ Icc (u + δ) v then
          w (Y q + J q) - w (Y q) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hpos : 0 < q := by
      have hsq : s < q := ((hT q).mp hq).1
      have hs0 : (0 : ℝ≥0) ≤ s := zero_le
      exact lt_of_le_of_lt hs0 hsq
    have hwq :
        w (riskProcess X x D q ω) -
          w (Function.leftLim
            (fun r : ℝ≥0 => riskProcess X x D r ω) q) =
        w (Y q + J q) - w (Y q) :=
      avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
        X x D hD w ω q hpos
    by_cases hstop : (q : ℝ≥0∞) ≤ ruinTime X x D ω
    · by_cases hband : Y q ∈ Icc (u + δ) v
      · simpa [hstop, hband] using hwq
      · simp [hstop, hband]
    · simp [hstop]
  exact hsum.trans hbase
