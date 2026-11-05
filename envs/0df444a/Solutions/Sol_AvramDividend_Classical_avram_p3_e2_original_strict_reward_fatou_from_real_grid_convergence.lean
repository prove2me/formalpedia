-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e2_original_strict_reward_fatou_from_real_grid_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:01:00.062834+00:00
-- url     : https://prove2.me/submissions/12bf5142-4004-4b94-b06d-32c472e24b59

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (Fmesh : ℕ → Ω → ℝ)
    (hConverge : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      Tendsto (fun n => Fmesh n ω) atTop (nhds ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)))) :
    ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
        liminf (fun n => ENNReal.ofReal (Fmesh n ω)) atTop := by
  filter_upwards [hConverge] with ω hω
  dsimp only at hω ⊢
  have hENN :=
    (ENNReal.continuous_ofReal.tendsto _).comp hω
  exact le_of_eq (hENN.liminf_eq).symm