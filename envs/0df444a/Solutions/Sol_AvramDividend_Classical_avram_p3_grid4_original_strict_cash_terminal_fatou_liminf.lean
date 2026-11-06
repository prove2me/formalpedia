-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:41:18.304195+00:00
-- url     : https://prove2.me/submissions/27ceedbf-5fc7-465d-a737-a491e8df8961

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original cash-prefix plus fixed surviving terminal has exact Fatou liminf. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω) (w : ℝ → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
    liminf (fun n : ℕ => ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0))) atTop := by
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let term : ℝ :=
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  let cash : ℕ → ℝ := fun n =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let fullCash : ℝ :=
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hCash : Tendsto cash atTop (𝓝 fullCash) := by
    simpa only [cash, fullCash] using
      (avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
        X x C D hD ω q hq T hT δ hδpos hδanti hδ)
  have hSum : Tendsto (fun n : ℕ => cash n + term) atTop
      (𝓝 (fullCash + term)) := hCash.add tendsto_const_nhds
  have hLift : Tendsto
      (fun n : ℕ => ENNReal.ofReal (cash n + term)) atTop
      (𝓝 (ENNReal.ofReal (fullCash + term))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hSum
  simpa only [S, term, cash, fullCash] using (le_of_eq hLift.liminf_eq.symm)
