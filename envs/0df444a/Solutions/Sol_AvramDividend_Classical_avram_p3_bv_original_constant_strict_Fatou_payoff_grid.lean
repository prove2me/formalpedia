-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_constant_strict_Fatou_payoff_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:56:08.050192+00:00
-- url     : https://prove2.me/submissions/e7c66fd0-90a8-467f-b7ca-d9e3302c6cef

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Original stopped strict cash plus terminal already supplies a
nonnegative integrable measurable (a.e.) constant Fatou payoff grid.
Only the genuine pathwise source inequality and compensated HJB drift
remain to be constructed separately. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    ∃ F : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let Strict : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  obtain ⟨f, hfm, hfi, hfn, hae⟩ :=
    avram_p3_bv_original_strict_reward_measurable_version
      X hBV x C D hD w hw_cont hw_neg q hq T hT hTpos hw_nonneg
  refine ⟨fun _ => f, (fun _ => hfm), (fun _ => hfi),
    (fun _ => hfn), ?_⟩
  filter_upwards [hae] with ω heq
  change ENNReal.ofReal (Strict ω) ≤
    liminf (fun _ : ℕ => ENNReal.ofReal (f ω)) atTop
  calc
    ENNReal.ofReal (Strict ω) = ENNReal.ofReal (f ω) :=
      congrArg ENNReal.ofReal heq.symm
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (f ω)) atTop := by simp
